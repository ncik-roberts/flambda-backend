open Asttypes
open Parsetree
open Jane_syntax_parsing

(****************************************)
(* Helpers used just within this module *)

module type Extension = sig
  val feature : Feature.t
end

module Ast_of (AST : AST)
              (Ext : Extension) : sig
  (* Wrap a bit of AST with a jane-syntax annotation *)
  val wrap_jane_syntax :
    string list ->   (* these strings describe the bit of new syntax *)
    ?payload:payload ->
    AST.ast ->
    AST.ast
end = struct
  let wrap_jane_syntax suffixes ?payload to_be_wrapped =
    AST.make_jane_syntax Ext.feature suffixes ?payload to_be_wrapped
end

module Of_ast (Ext : Extension) : sig
  module Desugaring_error : sig
    type error =
      | Not_this_embedding of Embedded_name.t
      | Non_embedding
  end

  type unwrapped := string list * payload * attributes

  (* Find and remove a jane-syntax attribute marker, returning an error
     if the attribute name does not have the right format or extension. *)
  val unwrap_jane_syntax_attributes :
    attributes -> (unwrapped, Desugaring_error.error) result

  (* The same as [unwrap_jane_syntax_attributes], except throwing
     an exception instead of returning an error.
  *)
  val unwrap_jane_syntax_attributes_exn :
    loc:Location.t -> attributes -> unwrapped
end = struct

  let extension_string = Feature.extension_component Ext.feature

  module Desugaring_error = struct
    type error =
      | Not_this_embedding of Embedded_name.t
      | Non_embedding

    let report_error ~loc = function
      | Not_this_embedding name ->
          Location.errorf ~loc
            "Tried to desugar the embedded term %a@ \
             as belonging to the %s extension"
            Embedded_name.pp_quoted_name name extension_string
      | Non_embedding ->
          Location.errorf ~loc
            "Tried to desugar a non-embedded expression@ \
             as belonging to the %s extension"
            extension_string

    exception Error of Location.t * error

    let () =
      Location.register_error_of_exn
        (function
          | Error(loc, err) ->
            Some (report_error ~loc err)
          | _ -> None)

    let raise ~loc err =
      raise (Error(loc, err))
  end

  let unwrap_jane_syntax_attributes attrs : (_, Desugaring_error.error) result =
    match find_and_remove_jane_syntax_attribute attrs with
    | Some (ext_name, _loc, payload, attrs) -> begin
        match Jane_syntax_parsing.Embedded_name.components ext_name with
        | extension_occur :: names
             when String.equal extension_occur extension_string ->
           Ok (names, payload, attrs)
        | _ -> Error (Not_this_embedding ext_name)
      end
    | None -> Error Non_embedding

  let unwrap_jane_syntax_attributes_exn ~loc attrs =
    match unwrap_jane_syntax_attributes attrs with
    | Ok x -> x
    | Error error -> Desugaring_error.raise ~loc error
end

(******************************************************************************)
(** Individual language extension modules *)

(* Note [Check for immutable extension in comprehensions code]
   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

   When we spot a comprehension for an immutable array, we need to make sure
   that both [comprehensions] and [immutable_arrays] are enabled.  But our
   general mechanism for checking for enabled extensions (in [of_ast]) won't
   work well here: it triggers when converting from
   e.g. [[%jane.non_erasable.comprehensions.array] ...] to the
   comprehensions-specific AST. But if we spot a
   [[%jane.non_erasable.comprehensions.immutable]], there is no expression to
   translate. So we just check for the immutable arrays extension when
   processing a comprehension expression for an immutable array.

   Note [Wrapping with make_entire_jane_syntax]
   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

   The topmost node in the encoded AST must always look like e.g.
   [%jane.non_erasable.comprehensions]. (More generally,
   [%jane.ERASABILITY.FEATURE] or [@jane.ERASABILITY.FEATURE].) This allows the
   decoding machinery to know what extension is being used and what function to
   call to do the decoding. Accordingly, during encoding, after doing the hard
   work of converting the extension syntax tree into e.g. Parsetree.expression,
   we need to make a final step of wrapping the result in a [%jane.*.xyz] node.
   Ideally, this step would be done by part of our general structure, like we
   separate [of_ast] and [of_ast_internal] in the decode structure; this design
   would make it structurally impossible/hard to forget taking this final step.

   However, the final step is only one line of code (a call to
   [make_entire_jane_syntax]), but yet the name of the feature varies, as does
   the type of the payload. It would thus take several lines of code to execute
   this command otherwise, along with dozens of lines to create the structure in
   the first place. And so instead we just manually call
   [make_entire_jane_syntax] and refer to this Note as a reminder to authors of
   future syntax features to remember to do this wrapping.

   Note [Outer attributes at end]
   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
   The order of attributes matters for several reasons:
   - If the user writes attributes on a Jane Street OCaml construct, where
     should those appear with respect to the Jane Syntax attribute that
     introduces the construct?
   - Some Jane Syntax embeddings use attributes, and sometimes an AST node will
     have multiple Jane Syntax-related attributes on it. Which attribute should
     Jane Syntax interpret first?

   Both of these questions are settled by a convention where attributes
   appearing later in an attribute list are considered to be "outer" to
   attributes appearing earlier. (ppxlib adopted this convention, and thus we
   need to as well for compatibility.)

   - User-written attributes appear later in the attribute list than
     a Jane Syntax attribute that introduces a syntactic construct.
   - If multiple Jane Syntax attributes appear on an AST node, the ones
     appearing later in the attribute list should be interpreted first.
*)

(** Layout annotations' encoding as attribute payload, used in both n-ary
    functions and layouts. *)
module Layout_annotation : sig
  module Encode : sig
    val as_payload : layout_annotation -> payload
    val option_list_as_payload : layout_annotation option list -> payload
  end

  module Decode : sig
    val from_payload : loc:Location.t -> payload -> layout_annotation
    val bound_vars_from_vars_and_payload :
      loc:Location.t -> string Location.loc list -> payload ->
      (string Location.loc * layout_annotation option) list
  end
end = struct
  module Desugaring_error = struct
    type error =
      | Not_a_layout of Parsetree.payload
      | Wrong_number_of_layouts of int * layout_annotation option list

    let report_error ~loc = function
      | Not_a_layout payload ->
          Location.errorf ~loc
            "Layout attribute does not name a layout:@;%a"
            (Printast.payload 0) payload
      | Wrong_number_of_layouts (n, layouts) ->
          Location.errorf ~loc
            "Wrong number of layouts in an layout attribute;@;\
             expecting %i but got this list:@;%a"
            n
            (Format.pp_print_list
               (Format.pp_print_option
                  ~none:(fun ppf () -> Format.fprintf ppf "None")
                  (Printast.layout_annotation 0)))
            layouts

    exception Error of Location.t * error

    let () =
      Location.register_error_of_exn
        (function
          | Error(loc, err) ->
              Some (report_error ~loc err)
          | _ -> None)

    let raise ~loc err =
      raise (Error(loc, err))
  end
  (*******************************************************)
  (* Conversions with a payload *)

  module Encode = struct
    let as_expr layout =
      (* CR layouts v1.5: revise when moving layout recognition away from parser*)
      let layout_string = match layout.txt with
        | Any -> "any"
        | Value -> "value"
        | Void -> "void"
        | Immediate64 -> "immediate64"
        | Immediate -> "immediate"
        | Float64 -> "float64"
      in
      Ast_helper.Exp.ident
        (Location.mkloc (Longident.Lident layout_string) layout.loc)

    let structure_item_of_expr expr =
      { pstr_desc = Pstr_eval (expr, []); pstr_loc = Location.none }

    let structure_item_of_none =
      { pstr_desc = Pstr_attribute { attr_name = Location.mknoloc "none"
                                   ; attr_payload = PStr []
                                   ; attr_loc = Location.none }
      ; pstr_loc = Location.none }

    let as_payload layout =
      let expr = as_expr layout in
      PStr [ structure_item_of_expr expr ]

    let option_list_as_payload layouts =
      let items =
        List.map (function
          | None -> structure_item_of_none
          | Some layout -> structure_item_of_expr (as_expr layout))
          layouts
      in
      PStr items
  end

  module Decode = struct
    exception Unexpected

    let from_expr = function
      | { pexp_desc = Pexp_ident layout_lid; _ } ->
        (* CR layouts v1.5: revise when moving layout recognition away from parser*)
        let layout = match Longident.last layout_lid.txt with
          | "any" -> Any
          | "value" -> Value
          | "void" -> Void
          | "immediate" -> Immediate
          | "immediate64" -> Immediate64
          | "float64" -> Float64
          | _ -> raise Unexpected
        in
        Location.mkloc layout layout_lid.loc
      | _ -> raise Unexpected

    let expr_of_structure_item = function
      | { pstr_desc = Pstr_eval (expr, _) } -> expr
      | _ -> raise Unexpected

    let is_none_structure_item = function
      | { pstr_desc = Pstr_attribute { attr_name = { txt = "none" } } } -> true
      | _ -> false

    let from_payload ~loc payload =
      try
        match payload with
        | PStr [ item ] -> from_expr (expr_of_structure_item item)
        | _ -> raise Unexpected
      with
        Unexpected -> Desugaring_error.raise ~loc (Not_a_layout payload)

    let option_list_from_payload ~loc payload =
      try
        match payload with
        | PStr items ->
          List.map (fun item ->
            if is_none_structure_item item
            then None
            else Some (from_expr (expr_of_structure_item item)))
            items
        | _ -> raise Unexpected
      with
        Unexpected -> Desugaring_error.raise ~loc (Not_a_layout payload)

    let bound_vars_from_vars_and_payload ~loc var_names payload =
      let layouts = option_list_from_payload ~loc payload in
      try
        List.combine var_names layouts
      with
      (* seems silly to check the length in advance when [combine] does *)
        Invalid_argument _ ->
        Desugaring_error.raise ~loc
          (Wrong_number_of_layouts(List.length var_names, layouts))
  end
end


(** List and array comprehensions *)
module Comprehensions = struct
  module Ext = struct
    let feature : Feature.t = Language_extension Comprehensions
  end

  module Ast_of = Ast_of (Expression) (Ext)
  module Of_ast = Of_ast (Ext)

  include Ext

  type iterator =
    | Range of { start     : expression
               ; stop      : expression
               ; direction : direction_flag }
    | In of expression

  type clause_binding =
    { pattern    : pattern
    ; iterator   : iterator
    ; attributes : attribute list }

  type clause =
    | For of clause_binding list
    | When of expression

  type comprehension =
    { body    : expression
    ; clauses : clause list
    }

  type expression =
    | Cexp_list_comprehension  of comprehension
    | Cexp_array_comprehension of mutable_flag * comprehension

  (* The desugared-to-OCaml version of comprehensions is described by the
     following BNF, where [{% '...' | expr %}] refers to the result of
     [Expression.make_jane_syntax] (via [comprehension_expr]) as described at
     the top of [jane_syntax_parsing.mli].

     {v
         comprehension ::=
           | {% 'comprehension.list' | '[' clauses ']' %}
           | {% 'comprehension.array' | '[|' clauses '|]' %}

         clauses ::=
           | {% 'comprehension.for' | 'let' iterator+ 'in' clauses %}
           | {% 'comprehension.when' | expr ';' clauses %}
           | {% 'comprehension.body' | expr %}

         iterator ::=
           | pattern '=' {% 'comprehension.for.range.upto' | expr ',' expr %}
           | pattern '=' {% 'comprehension.for.range.downto' | expr ',' expr %}
           | pattern '=' {% 'comprehension.for.in' | expr %}
     v}
  *)

  (** First, we define how to go from the nice AST to the OCaml AST; this is
      the [expr_of_...] family of expressions, culminating in
      [expr_of_comprehension_expr]. *)

  let expr_of_iterator = function
    | Range { start; stop; direction } ->
        Ast_of.wrap_jane_syntax
          [ "for"
          ; "range"
          ; match direction with
            | Upto   -> "upto"
            | Downto -> "downto" ]
          (Ast_helper.Exp.tuple [start; stop])
    | In seq ->
        Ast_of.wrap_jane_syntax ["for"; "in"] seq

  let expr_of_clause_binding { pattern; iterator; attributes } =
    Ast_helper.Vb.mk ~attrs:attributes pattern (expr_of_iterator iterator)

  let expr_of_clause clause rest = match clause with
    | For iterators ->
        Ast_of.wrap_jane_syntax
          ["for"]
          (Ast_helper.Exp.let_
             Nonrecursive (List.map expr_of_clause_binding iterators)
             rest)
    | When cond ->
        Ast_of.wrap_jane_syntax ["when"] (Ast_helper.Exp.sequence cond rest)

  let expr_of_comprehension ~type_ { body; clauses } =
    (* We elect to wrap the body in a new AST node (here, [Pexp_lazy])
       because it makes it so there is no AST node that can carry multiple Jane
       Syntax-related attributes in addition to user-written attributes. This
       choice simplifies the definition of [comprehension_expr_of_expr], as
       part of its contract is threading through the user-written attributes
       on the outermost node.
    *)
    Ast_of.wrap_jane_syntax
      type_
      (Ast_helper.Exp.lazy_
        (List.fold_right
          expr_of_clause
          clauses
          (Ast_of.wrap_jane_syntax ["body"] body)))

  let expr_of ~loc cexpr =
    (* See Note [Wrapping with make_entire_jane_syntax] *)
    Expression.make_entire_jane_syntax ~loc feature (fun () ->
      match cexpr with
      | Cexp_list_comprehension comp ->
          expr_of_comprehension ~type_:["list"] comp
      | Cexp_array_comprehension (amut, comp) ->
          expr_of_comprehension
            ~type_:[ "array"
                   ; match amut with
                     | Mutable   -> "mutable"
                     | Immutable -> "immutable"
                   ]
            comp)

  (** Then, we define how to go from the OCaml AST to the nice AST; this is
      the [..._of_expr] family of expressions, culminating in
      [comprehension_expr_of_expr]. *)

  module Desugaring_error = struct
    type error =
      | Has_payload of payload
      | Bad_comprehension_embedding of string list
      | No_clauses

    let report_error ~loc = function
      | Has_payload payload ->
          Location.errorf ~loc
            "Comprehensions attribute has an unexpected payload:@;%a"
            (Printast.payload 0) payload
      | Bad_comprehension_embedding subparts ->
          Location.errorf ~loc
            "Unknown, unexpected, or malformed@ comprehension embedded term %a"
            Embedded_name.pp_quoted_name
            (Embedded_name.of_feature feature subparts)
      | No_clauses ->
          Location.errorf ~loc
            "Tried to desugar a comprehension with no clauses"

    exception Error of Location.t * error

    let () =
      Location.register_error_of_exn
        (function
          | Error(loc, err) -> Some (report_error ~loc err)
          | _ -> None)

    let raise expr err = raise (Error(expr.pexp_loc, err))
  end

  (* Returns the expression node with the outermost Jane Syntax-related
     attribute removed. *)
  let expand_comprehension_extension_expr expr =
    let names, payload, attributes =
      Of_ast.unwrap_jane_syntax_attributes_exn
        ~loc:expr.pexp_loc expr.pexp_attributes
    in
    match payload with
    | PStr [] -> names, { expr with pexp_attributes = attributes }
    | _ -> Desugaring_error.raise expr (Has_payload payload)

  let iterator_of_expr expr =
    match expand_comprehension_extension_expr expr with
    | ["for"; "range"; "upto"],
      { pexp_desc = Pexp_tuple [start; stop]; _ } ->
        Range { start; stop; direction = Upto }
    | ["for"; "range"; "downto"],
      { pexp_desc = Pexp_tuple [start; stop]; _ } ->
        Range { start; stop; direction = Downto }
    | ["for"; "in"], seq ->
        In seq
    | bad, _ ->
        Desugaring_error.raise expr (Bad_comprehension_embedding bad)

  let clause_binding_of_vb { pvb_pat; pvb_expr; pvb_attributes; pvb_loc = _ } =
    { pattern = pvb_pat
    ; iterator = iterator_of_expr pvb_expr
    ; attributes = pvb_attributes }

  let add_clause clause comp = { comp with clauses = clause :: comp.clauses }

  let comprehension_of_expr =
    let rec raw_comprehension_of_expr expr =
      match expand_comprehension_extension_expr expr with
      | ["for"], { pexp_desc = Pexp_let(Nonrecursive, iterators, rest); _ } ->
          add_clause
            (For (List.map clause_binding_of_vb iterators))
            (raw_comprehension_of_expr rest)
      | ["when"], { pexp_desc = Pexp_sequence(cond, rest); _ } ->
          add_clause
            (When cond)
            (raw_comprehension_of_expr rest)
      | ["body"], body ->
          { body; clauses = [] }
      | bad, _ ->
          Desugaring_error.raise expr (Bad_comprehension_embedding bad)
    in
    fun expr ->
      match raw_comprehension_of_expr expr with
      | { body = _; clauses = [] } ->
          Desugaring_error.raise expr No_clauses
      | comp -> comp

  (* Returns remaining unconsumed attributes on outermost expression *)
  let comprehension_expr_of_expr expr =
    let name, wrapper = expand_comprehension_extension_expr expr in
    let comp =
      match name, wrapper.pexp_desc with
      | ["list"], Pexp_lazy comp ->
          Cexp_list_comprehension (comprehension_of_expr comp)
      | ["array"; "mutable"], Pexp_lazy comp ->
          Cexp_array_comprehension (Mutable, comprehension_of_expr comp)
      | ["array"; "immutable"], Pexp_lazy comp ->
          (* assert_extension_enabled:
            See Note [Check for immutable extension in comprehensions code] *)
          assert_extension_enabled ~loc:expr.pexp_loc Immutable_arrays ();
          Cexp_array_comprehension (Immutable, comprehension_of_expr comp)
      | bad, _ ->
          Desugaring_error.raise expr (Bad_comprehension_embedding bad)
    in
    comp, wrapper.pexp_attributes
end

(** Immutable arrays *)
module Immutable_arrays = struct
  type nonrec expression =
    | Iaexp_immutable_array of expression list

  type nonrec pattern =
    | Iapat_immutable_array of pattern list

  let feature : Feature.t = Language_extension Immutable_arrays

  let expr_of ~loc = function
    | Iaexp_immutable_array elts ->
      (* See Note [Wrapping with make_entire_jane_syntax] *)
      Expression.make_entire_jane_syntax ~loc feature (fun () ->
        Ast_helper.Exp.array elts)

  (* Returns remaining unconsumed attributes *)
  let of_expr expr = match expr.pexp_desc with
    | Pexp_array elts -> Iaexp_immutable_array elts, expr.pexp_attributes
    | _ -> failwith "Malformed immutable array expression"

  let pat_of ~loc = function
    | Iapat_immutable_array elts ->
      (* See Note [Wrapping with make_entire_jane_syntax] *)
      Pattern.make_entire_jane_syntax ~loc feature (fun () ->
        Ast_helper.Pat.array elts)

  (* Returns remaining unconsumed attributes *)
  let of_pat pat = match pat.ppat_desc with
    | Ppat_array elts -> Iapat_immutable_array elts, pat.ppat_attributes
    | _ -> failwith "Malformed immutable array pattern"
end

module N_ary_functions = struct
  module Ext = struct
    let feature : Feature.t = Builtin
  end

  module Layout = struct
    module Ext = struct
      let feature : Feature.t = Language_extension Layouts
    end

    module Ast_of = Ast_of (Expression) (Ext)
    module Of_ast = Of_ast (Ext)
  end

  module Ast_of = Ast_of (Expression) (Ext)
  module Of_ast = Of_ast (Ext)
  open Ext

  type function_body =
    | Pfunction_body of expression
    | Pfunction_cases of case list * Location.t * attributes

  type function_param =
    | Pparam_val of arg_label * expression option * pattern
    | Pparam_newtype of string loc * layout_annotation option * Location.t

  type type_constraint =
    | Pconstraint of core_type
    | Pcoerce of core_type option * core_type

  type alloc_mode = Local | Global

  type function_constraint =
    { alloc_mode: alloc_mode;
      type_constraint: type_constraint;
    }

  type expression =
    function_param list * function_constraint option * function_body

  module Extension_node = struct
    type n_ary =
      | Param
      | End_expression_body
      | End_cases
      | Alloc_mode of alloc_mode

    let to_extension_suffix = function
      | Param -> [ "param" ]
      | End_expression_body -> ["end" ]
      | End_cases -> ["end"; "cases" ]
      | Alloc_mode Global -> [ "alloc_mode"; "global" ]
      | Alloc_mode Local -> [ "alloc_mode"; "local" ]

    let of_extension_suffix = function
      | [ "param" ] -> Some Param
      | [ "end" ] -> Some End_expression_body
      | [ "end"; "cases" ] -> Some End_cases
      | [ "alloc_mode"; "global" ] -> Some (Alloc_mode Global)
      | [ "alloc_mode"; "local" ] -> Some (Alloc_mode Local)
      | _ -> None

    let format ppf t =
      Embedded_name.pp_quoted_name
        ppf
        (Embedded_name.of_feature feature (to_extension_suffix t))

    type t =
      | N_ary of n_ary
      | Layout_annotation of layout_annotation
  end

  let layout_annotation_components = [ "annotation" ]

  module Extension_node_with_payload = struct
    type t =
      | Param
      | End_expression_body
      | End_cases of case list
      | Alloc_mode of alloc_mode
      | Layout_annotation of
          layout_annotation * string loc * Parsetree.expression
  end

  module Desugaring_error = struct
    type error =
      | Has_payload of payload
      | Missing_closing_embedding
      | Missing_alloc_mode
      | Misannotated_function_cases
      | Misannotated_layout
      | Bad_syntactic_arity_embedding of string list

    let report_error ~loc = function
      | Has_payload payload ->
          Location.errorf ~loc
            "N-ary function attribute has an unexpected payload:@;%a"
            (Printast.payload 0) payload
      | Missing_closing_embedding ->
          Location.errorf ~loc
            "Expected a syntactic-arity embedding delimiting the end of \
             the n-ary function before reaching a node of this kind. The only \
             legal construct is a nested sequence of Pexp_fun and Pexp_newtype \
             nodes, optionally followed by a Pexp_coerce or Pexp_constraint \
             node, followed by a node with a %a or %a attribute."
            Extension_node.format Extension_node.End_cases
            Extension_node.format Extension_node.End_expression_body
      | Missing_alloc_mode ->
          Location.errorf ~loc
            "Expected the alloc mode to be indicated on a Pexp_coerce or \
             Pexp_constraint node within an n-ary function: one of \
             %a or %a."
            Extension_node.format (Extension_node.Alloc_mode Global)
            Extension_node.format (Extension_node.Alloc_mode Local)
      | Misannotated_function_cases ->
          Location.errorf ~loc
            "%a may be applied only to a function expression."
            Extension_node.format Extension_node.End_cases
      | Misannotated_layout ->
          Location.errorf ~loc
            "A layout annotation in an n-ary function expression may only \
             be applied to Pexp_newtype."
      | Bad_syntactic_arity_embedding suffix ->
          Location.errorf ~loc
            "Unknown syntactic-arity extension point %a."
            Embedded_name.pp_quoted_name
            (Embedded_name.of_feature feature suffix)

    exception Error of Location.t * error

    let () =
      Location.register_error_of_exn
        (function
          | Error(loc, err) -> Some (report_error ~loc err)
          | _ -> None)

    let raise expr err = raise (Error (expr.pexp_loc, err))
  end

  let expand_n_ary_expr expr =
    match Of_ast.unwrap_jane_syntax_attributes expr.pexp_attributes with
    | Error Non_embedding -> None
    | Error (Not_this_embedding _) -> begin
        let suffix, payload, attributes =
          Layout.Of_ast.unwrap_jane_syntax_attributes_exn
            ~loc:expr.pexp_loc
            expr.pexp_attributes
        in
        if suffix = layout_annotation_components then begin
          let layout_annotation =
            Layout_annotation.Decode.from_payload payload ~loc:expr.pexp_loc
          in
          let expr = { expr with pexp_attributes = attributes } in
          Some (Extension_node.Layout_annotation layout_annotation, expr)
       end else
          Desugaring_error.raise expr (Bad_syntactic_arity_embedding suffix)
      end
    | Ok (suffix, payload, attributes) -> begin
        let () =
          match payload with
          | PStr [] -> ()
          | _ -> Desugaring_error.raise expr (Has_payload payload)
        in
        let expr = { expr with pexp_attributes = attributes } in
        match Extension_node.of_extension_suffix suffix with
        | Some ext -> Some (Extension_node.N_ary ext, expr)
        | None ->
            Desugaring_error.raise
              expr
              (Bad_syntactic_arity_embedding suffix)
      end

  let expand_n_ary_expr_with_payload expr
      : (Extension_node_with_payload.t * Parsetree.expression) option
    =
    match expand_n_ary_expr expr with
    | None -> None
    | Some (Param, expr) -> Some (Param, expr)
    | Some (End_expression_body, expr) -> Some (End_expression_body, expr)
    | Some (End_cases, ({ pexp_desc = Pexp_function cases } as expr)) ->
        Some (End_cases cases, expr)
    | Some (N_ary End_cases, expr) ->
        Desugaring_error.raise expr Misannotated_function_cases
    | Some (N_ary End_expression_body, expr) -> Some (End_expression_body, expr)
    | Some (N_ary (Alloc_mode alloc_mode), expr) ->
        Some (Alloc_mode alloc_mode, expr)
    | Some (Layout_annotation annotation,
            ({ pexp_desc = Pexp_newtype (ty, body) } as expr)) ->
        Some (Layout_annotation (annotation, ty, body), expr)
    | Some (Layout_annotation _, expr) ->
        Desugaring_error.raise expr Misannotated_layout

  let check_end expr ~rev_params ~function_constraint =
    match expand_n_ary_expr_with_payload expr with
    | Some (Param, _) | Some (Alloc_mode _, _) -> None
    | Some (End_cases cases, expr) ->
        let { pexp_loc = loc; pexp_attributes = attrs } = expr in
        let params = List.rev rev_params in
        Some (`End (params, function_constraint, Pfunction_cases (cases, loc, attrs)))
    | Some (End_expression_body, expr) ->
        let params = List.rev rev_params in
        Some (params, function_constraint, Pfunction_body expr)
    | None ->
        (* In this case, the node is not marked with any Jane Syntax attribute.
           It may seem surprising that we don't raise an error, as it would seem
           the AST is invalid by the invariants of the Jane Syntax library.
           We don't raise an error because we permit ppxes to drop the final
           [End_expression_body] attribute. Lots of existing ppxes do this in
           the course of rewriting functions, and it's difficult to change them
           all to not drop this attribute. Instead, we consider the absence of
           any Jane Syntax attribute to be equivalent to [End_expression_body].

           Note we'll still loudly complain if we see a *misplaced* Jane Syntax
           attribute.
        *)
        let params = List.rev rev_params in
        Some (params, function_constraint, Pfunction_body expr)

  let require_alloc_mode expr =
    match expand_n_ary_expr expr with
    | Some (N_ary Alloc_mode alloc_mode, _) -> alloc_mode
    | _ -> Desugaring_error.raise expr Missing_alloc_mode

  let require_end expr ~rev_params ~type_constraint ~alloc_mode =
    match
      check_end
        expr
        ~rev_params
        ~function_constraint:(Some { type_constraint; alloc_mode })
    with
    | Some (`End result) -> result
    | Some (`Layout_annotation _) | None ->
        Desugaring_error.raise expr Missing_closing_embedding

  (* Returns remaining unconsumed attributes on outermost expression *)
  let of_expr =
    let rec loop expr ~rev_params =
      match check_end expr ~function_constraint:None ~rev_params with
      | Some (`End result) -> result
      | Some (`Layout_annotation (annotation, ty, body)) ->
          let loc = { ty.loc with loc_ghost = true } in
          let param = Pparam_newtype (ty, Some annotation, loc) in
          loop body ~rev_params:(param :: rev_params)
      | None -> begin
          match expr.pexp_desc with
          | Pexp_fun (label, default, pat, body) ->
              let param = Pparam_val (label, default, pat) in
              loop body ~rev_params:(param :: rev_params)
          | Pexp_newtype (newtype, body) ->
              let loc = { newtype.loc with loc_ghost = true } in
              let param = Pparam_newtype (newtype, None, loc) in
              loop body ~rev_params:(param :: rev_params)
          | Pexp_constraint (body, ty) ->
              let alloc_mode = require_alloc_mode expr in
              let type_constraint = Pconstraint ty in
              require_end body ~rev_params ~alloc_mode ~type_constraint
          | Pexp_coerce (body, ty1, ty2) ->
              let alloc_mode = require_alloc_mode expr in
              let type_constraint = Pcoerce (ty1, ty2) in
              require_end body ~rev_params ~alloc_mode ~type_constraint
          | _ -> Desugaring_error.raise expr Missing_closing_embedding
        end
    in
    fun expr ->
      match expr.pexp_desc with
      | Pexp_function _ | Pexp_fun _ | Pexp_newtype _ -> begin
          match expand_n_ary_expr_with_payload expr with
          | Some (End_cases cases, expr) ->
              (* If the outermost node is [End_cases], we place the attributes
                 on the function node as a whole rather than on the
                 [Pfunction_cases] body.
              *)
              let { pexp_loc = loc; pexp_attributes = attrs } = expr in
              let n_ary =
                [], None, Pfunction_cases (cases, loc, [])
              in
              Some (n_ary, attrs)
          | expanded ->
              let unconsumed_attributes =
                match expanded with
                | None -> expr.pexp_attributes
                | Some (_, { pexp_attributes }) -> pexp_attributes
              in
              Some (loop expr ~rev_params:[], unconsumed_attributes)
      end
      | _ -> None

  let n_ary_function_expr ext x =
    let suffix = Extension_node.to_extension_suffix ext in
    Ast_of.wrap_jane_syntax suffix x

  let expr_of ~loc (params, constraint_, body) =
    (* See Note [Wrapping with make_entire_jane_syntax] *)
    Expression.make_entire_jane_syntax ~loc feature (fun () ->
      let body =
        match body with
        | Pfunction_body body ->
            n_ary_function_expr End_expression_body body
        | Pfunction_cases (cases, loc, attrs) ->
            n_ary_function_expr End_cases
              (Ast_helper.Exp.function_ cases ~loc ~attrs)
      in
      let constrained_body =
        match constraint_ with
        | None -> body
        | Some { type_constraint; alloc_mode } ->
            n_ary_function_expr (Alloc_mode alloc_mode)
              (match type_constraint with
              | Pconstraint ty -> Ast_helper.Exp.constraint_ body ty
              | Pcoerce (ty1, ty2) -> Ast_helper.Exp.coerce body ty1 ty2)
      in
      List.fold_right
        (fun param body ->
          n_ary_function_expr Param (
            match param with
            | Pparam_val (label, default, pat) ->
                Ast_helper.Exp.fun_ label default pat body
            | Pparam_newtype (newtype, None, loc) ->
                Ast_helper.Exp.newtype newtype body ~loc
            | Pparam_newtype (newtype, Some annotation, loc) ->
                Layout.Ast_of.wrap_jane_syntax
                  layout_annotation_components
                  ~payload:(Layout_annotation.Encode.as_payload annotation)
                  (Ast_helper.Exp.newtype newtype body ~loc)))
        params
        constrained_body)
end

(** [include functor] *)
module Include_functor = struct
  type signature_item =
    | Ifsig_include_functor of include_description

  type structure_item =
    | Ifstr_include_functor of include_declaration

  let feature : Feature.t = Language_extension Include_functor

  let sig_item_of ~loc = function
    | Ifsig_include_functor incl ->
        (* See Note [Wrapping with make_entire_jane_syntax] *)
        Signature_item.make_entire_jane_syntax ~loc feature (fun () ->
          Ast_helper.Sig.include_ incl)

  let of_sig_item sigi = match sigi.psig_desc with
    | Psig_include incl -> Ifsig_include_functor incl
    | _ -> failwith "Malformed [include functor] in signature"

  let str_item_of ~loc = function
    | Ifstr_include_functor incl ->
        (* See Note [Wrapping with make_entire_jane_syntax] *)
        Structure_item.make_entire_jane_syntax ~loc feature (fun () ->
          Ast_helper.Str.include_ incl)

  let of_str_item stri = match stri.pstr_desc with
    | Pstr_include incl -> Ifstr_include_functor incl
    | _ -> failwith "Malformed [include functor] in structure"
end

(** Module strengthening *)
module Strengthen = struct
  type nonrec module_type =
    { mty : Parsetree.module_type; mod_id : Longident.t Location.loc }

  let feature : Feature.t = Language_extension Module_strengthening

  (* Encoding: [S with M] becomes [functor (_ : S) -> (module M)], where
     the [(module M)] is a [Pmty_alias].  This isn't syntax we can write, but
     [(module M)] can be the inferred type for [M], so this should be fine. *)

  let mty_of ~loc { mty; mod_id } =
    (* See Note [Wrapping with make_entire_jane_syntax] *)
    Module_type.make_entire_jane_syntax ~loc feature (fun () ->
      Ast_helper.Mty.functor_ (Named (Location.mknoloc None, mty))
        (Ast_helper.Mty.alias mod_id))

  (* Returns remaining unconsumed attributes *)
  let of_mty mty = match mty.pmty_desc with
    | Pmty_functor(Named(_, mty), {pmty_desc = Pmty_alias mod_id}) ->
       { mty; mod_id }, mty.pmty_attributes
    | _ -> failwith "Malformed strengthened module type"
end

(** Layouts *)
module Layouts = struct
  module Ext = struct
    let feature : Feature.t = Language_extension Layouts
  end

  include Ext

  module Of_ast = Of_ast (Ext)

  type constant =
    | Float of string * char option
    | Integer of string * char

  type nonrec expression =
    | Lexp_constant of constant
    | Lexp_newtype of string loc * layout_annotation * expression

  type nonrec pattern =
    | Lpat_constant of constant

  type nonrec core_type =
    | Ltyp_var of { name : string option
                  ; layout : Asttypes.layout_annotation }
    | Ltyp_poly of { bound_vars : (string loc * layout_annotation option) list
                   ; inner_type : core_type }
    | Ltyp_alias of { aliased_type : core_type
                    ; name : string option
                    ; layout : Asttypes.layout_annotation }

  type nonrec extension_constructor =
    | Lext_decl of (string Location.loc *
                    Asttypes.layout_annotation option) list *
                   constructor_arguments *
                   Parsetree.core_type option

  (*******************************************************)
  (* Errors *)

  module Desugaring_error = struct
    type error =
      | Unexpected_wrapped_type of Parsetree.core_type
      | Unexpected_wrapped_ext of Parsetree.extension_constructor
      | Unexpected_attribute of string list
      | No_integer_suffix
      | Unexpected_constant of Parsetree.constant
      | Unexpected_wrapped_expr of Parsetree.expression
      | Unexpected_wrapped_pat of Parsetree.pattern

    let report_error ~loc = function
      | Unexpected_wrapped_type typ ->
        Location.errorf ~loc
          "Layout attribute on wrong core type:@;%a"
          (Printast.core_type 0) typ
      | Unexpected_wrapped_ext ext ->
        Location.errorf ~loc
          "Layout attribute on wrong extension constructor:@;%a"
          (Printast.extension_constructor 0) ext
      | Unexpected_attribute names ->
        Location.errorf ~loc
          "Layout extension does not understand these attribute names:@;[%a]"
          (Format.pp_print_list
             ~pp_sep:(fun ppf () -> Format.fprintf ppf ";@ ")
             Format.pp_print_text) names
      | No_integer_suffix ->
        Location.errorf ~loc
          "All unboxed integers require a suffix to determine their size."
      | Unexpected_constant c ->
        Location.errorf ~loc
          "Unexpected unboxed constant:@ %a"
          (Printast.constant) c
      | Unexpected_wrapped_expr expr ->
        Location.errorf ~loc
          "Layout attribute on wrong expression:@;%a"
          (Printast.expression 0) expr
      | Unexpected_wrapped_pat pat ->
        Location.errorf ~loc
          "Layout attribute on wrong pattern:@;%a"
          (Printast.pattern 0) pat

    exception Error of Location.t * error

    let () =
      Location.register_error_of_exn
        (function
          | Error(loc, err) -> Some (report_error ~loc err)
          | _ -> None)

    let raise ~loc err = raise (Error(loc, err))
  end

  module Encode = Layout_annotation.Encode
  module Decode = Layout_annotation.Decode

  (*******************************************************)
  (* Constants *)

  let constant_of = function
    | Float (x, suffix) -> Pconst_float (x, suffix)
    | Integer (x, suffix) -> Pconst_integer (x, Some suffix)

  let of_constant ~loc = function
    | Pconst_float (x, suffix) -> Float (x, suffix)
    | Pconst_integer (x, Some suffix) -> Integer (x, suffix)
    | Pconst_integer (_, None) ->
      Desugaring_error.raise ~loc No_integer_suffix
    | const -> Desugaring_error.raise ~loc (Unexpected_constant const)

  (*******************************************************)
  (* Encoding expressions *)

  let expr_of ~loc expr =
    let module Ast_of = Ast_of (Expression) (Ext) in
    (* See Note [Wrapping with make_entire_jane_syntax] *)
    Expression.make_entire_jane_syntax ~loc feature begin fun () ->
      match expr with
      | Lexp_constant c ->
        let constant = constant_of c in
        Ast_of.wrap_jane_syntax ["unboxed"] @@
        Ast_helper.Exp.constant constant
      | Lexp_newtype (name, layout, inner_expr) ->
        let payload = Encode.as_payload layout in
        Ast_of.wrap_jane_syntax ["newtype"] ~payload @@
        Ast_helper.Exp.newtype name inner_expr
    end

  (*******************************************************)
  (* Desugaring expressions *)

  let of_expr expr =
    let loc = expr.pexp_loc in
    let names, payload, attributes =
      Of_ast.unwrap_jane_syntax_attributes_exn ~loc expr.pexp_attributes
    in
    let lexpr = match names with
      | [ "unboxed" ] ->
        begin match expr.pexp_desc with
        | Pexp_constant const -> Lexp_constant (of_constant ~loc const)
        | _ -> Desugaring_error.raise ~loc (Unexpected_wrapped_expr expr)
        end
      | [ "newtype" ] ->
        let layout = Decode.from_payload ~loc payload in
        begin match expr.pexp_desc with
        | Pexp_newtype (name, inner_expr) ->
          Lexp_newtype (name, layout, inner_expr)
        | _ -> Desugaring_error.raise ~loc (Unexpected_wrapped_expr expr)
        end
      | _ -> Desugaring_error.raise ~loc (Unexpected_attribute names)
    in
    lexpr, attributes

  (*******************************************************)
  (* Encoding patterns *)

  let pat_of ~loc t =
    Pattern.make_entire_jane_syntax ~loc feature begin fun () ->
      match t with
      | Lpat_constant c ->
        let constant = constant_of c in
        Ast_helper.Pat.constant constant
    end

  (*******************************************************)
  (* Desugaring patterns *)

  let of_pat pat =
    let loc = pat.ppat_loc in
    let lpat = match pat.ppat_desc with
      | Ppat_constant const -> Lpat_constant (of_constant ~loc const)
      | _ -> Desugaring_error.raise ~loc (Unexpected_wrapped_pat pat)
    in
    lpat, pat.ppat_attributes

  (*******************************************************)
  (* Encoding types *)

  module Type_of = Ast_of (Core_type) (Ext)

  let type_of ~loc typ =
    let exception No_wrap_necessary of Parsetree.core_type in
    try
      (* See Note [Wrapping with make_entire_jane_syntax] *)
      Core_type.make_entire_jane_syntax ~loc feature begin fun () ->
        match typ with
        | Ltyp_var { name; layout } ->
          let payload = Encode.as_payload layout in
          Type_of.wrap_jane_syntax ["var"] ~payload @@
          begin match name with
          | None -> Ast_helper.Typ.any ~loc ()
          | Some name -> Ast_helper.Typ.var ~loc name
          end
        | Ltyp_poly { bound_vars; inner_type } ->
          let var_names, layouts = List.split bound_vars in
          (* Pass the loc because we don't want a ghost location here *)
          let tpoly = Ast_helper.Typ.poly ~loc var_names inner_type in
          if List.for_all Option.is_none layouts
          then raise (No_wrap_necessary tpoly)
          else
            let payload = Encode.option_list_as_payload layouts in
            Type_of.wrap_jane_syntax ["poly"] ~payload tpoly

        | Ltyp_alias { aliased_type; name; layout } ->
          let payload = Encode.as_payload layout in
          let has_name, inner_typ = match name with
            | None -> "anon", aliased_type
            | Some name -> "named", Ast_helper.Typ.alias aliased_type name
          in
          Type_of.wrap_jane_syntax ["alias"; has_name] ~payload inner_typ
      end
    with
      No_wrap_necessary result_type -> result_type

  (*******************************************************)
  (* Desugaring types *)

  let of_type typ =
    let loc = typ.ptyp_loc in
    let names, payload, attributes =
      Of_ast.unwrap_jane_syntax_attributes_exn ~loc typ.ptyp_attributes
    in
    let lty = match names with
      | [ "var" ] ->
        let layout = Decode.from_payload ~loc payload in
        begin match typ.ptyp_desc with
        | Ptyp_any ->
          Ltyp_var { name = None; layout }
        | Ptyp_var name ->
          Ltyp_var { name = Some name; layout }
        | _ -> Desugaring_error.raise ~loc (Unexpected_wrapped_type typ)
        end

      | [ "poly" ] ->
        begin match typ.ptyp_desc with
        | Ptyp_poly (var_names, inner_type) ->
          let bound_vars =
            Decode.bound_vars_from_vars_and_payload ~loc var_names payload
          in
          Ltyp_poly { bound_vars; inner_type }
        | _ -> Desugaring_error.raise ~loc (Unexpected_wrapped_type typ)
        end

      | [ "alias"; "anon" ] ->
        let layout = Decode.from_payload ~loc payload in
        Ltyp_alias { aliased_type = { typ with ptyp_attributes = attributes }
                   ; name = None
                   ; layout }

      | [ "alias"; "named" ] ->
        let layout = Decode.from_payload ~loc payload in
        begin match typ.ptyp_desc with
        | Ptyp_alias (inner_typ, name) ->
          Ltyp_alias { aliased_type = inner_typ
                     ; name = Some name
                     ; layout }

        | _ -> Desugaring_error.raise ~loc (Unexpected_wrapped_type typ)
        end

      | _ ->
        Desugaring_error.raise ~loc (Unexpected_attribute names)
    in
    lty, attributes

  (*******************************************************)
  (* Encoding extension constructor *)

  module Ext_ctor_of = Ast_of (Extension_constructor) (Ext)

  let extension_constructor_of ~loc ~name ?info ?docs ext =
    (* using optional parameters to hook into existing defaulting
       in [Ast_helper.Te.decl], which seems unwise to duplicate *)
    let exception No_wrap_necessary of Parsetree.extension_constructor in
    try
      (* See Note [Wrapping with make_entire_jane_syntax] *)
        Extension_constructor.make_entire_jane_syntax ~loc feature
          begin fun () ->
            match ext with
            | Lext_decl (bound_vars, args, res) ->
              let vars, layouts = List.split bound_vars in
              let ext_ctor =
                (* Pass ~loc here, because the constructor declaration is
                   not a ghost *)
                Ast_helper.Te.decl ~loc ~vars ~args ?info ?docs ?res name
              in
              if List.for_all Option.is_none layouts
              then raise (No_wrap_necessary ext_ctor)
              else
                let payload = Encode.option_list_as_payload layouts in
                Ext_ctor_of.wrap_jane_syntax ["ext"] ~payload ext_ctor
          end
    with
      No_wrap_necessary ext_ctor -> ext_ctor

  (*******************************************************)
  (* Desugaring extension constructor *)

  let of_extension_constructor ext =
    let loc = ext.pext_loc in
    let names, payload, attributes =
      Of_ast.unwrap_jane_syntax_attributes_exn ~loc ext.pext_attributes
    in
    let lext = match names with
      | [ "ext" ] ->
        begin match ext.pext_kind with
        | Pext_decl (var_names, args, res) ->
          let bound_vars =
            Decode.bound_vars_from_vars_and_payload ~loc var_names payload
          in
          Lext_decl (bound_vars, args, res)
        | _ -> Desugaring_error.raise ~loc (Unexpected_wrapped_ext ext)
        end

      | _ ->
        Desugaring_error.raise ~loc (Unexpected_attribute names)
    in
    lext, attributes

  (*********************************************************)
  (* Constructing a [constructor_declaration] with layouts *)

  module Ctor_decl_of = Ast_of (Constructor_declaration) (Ext)

  let constructor_declaration_of ~loc ~info ~attrs ~vars_layouts ~args
        ~res name =
    let vars, layouts = List.split vars_layouts in
    let ctor_decl =
      Ast_helper.Type.constructor ~loc ~info ~vars ~args ?res name
    in
    let ctor_decl =
      if List.for_all Option.is_none layouts
      then ctor_decl
      else
        let payload = Encode.option_list_as_payload layouts in
        Constructor_declaration.make_entire_jane_syntax ~loc feature
          begin fun () ->
            Ctor_decl_of.wrap_jane_syntax ["vars"] ~payload ctor_decl
          end
    in
    (* See Note [Outer attributes at end] *)
    { ctor_decl with pcd_attributes = ctor_decl.pcd_attributes @ attrs }

  let of_constructor_declaration_internal (feat : Feature.t) ctor_decl =
    match feat with
    | Language_extension Layouts ->
      let loc = ctor_decl.pcd_loc in
      let names, payload, attributes =
        Of_ast.unwrap_jane_syntax_attributes_exn ~loc ctor_decl.pcd_attributes
      in
      let vars_layouts = match names with
        | [ "vars" ] ->
          Decode.bound_vars_from_vars_and_payload
            ~loc ctor_decl.pcd_vars payload
        | _ -> Desugaring_error.raise ~loc (Unexpected_attribute names)
      in
      Some (vars_layouts, attributes)
    | _ -> None

  let of_constructor_declaration =
    Constructor_declaration.make_of_ast
       ~of_ast_internal:of_constructor_declaration_internal
end

(******************************************************************************)
(** The interface to our novel syntax, which we export *)

module type AST = sig
  type t
  type ast

  val of_ast : ast -> t option
end

module Core_type = struct
  type t =
    | Jtyp_layout of Layouts.core_type

  let of_ast_internal (feat : Feature.t) typ = match feat with
    | Language_extension Layouts ->
      let typ, attrs = Layouts.of_type typ in
      Some (Jtyp_layout typ, attrs)
    | _ -> None

  let of_ast = Core_type.make_of_ast ~of_ast_internal

  let core_type_of ~loc ~attrs t =
    let core_type =
      match t with
      | Jtyp_layout x -> Layouts.type_of ~loc x
    in
    (* See Note [Outer attributes at end] *)
    { core_type with ptyp_attributes = core_type.ptyp_attributes @ attrs }
end

module Constructor_argument = struct
  type t = |

  let of_ast_internal (feat : Feature.t) _carg = match feat with
    | _ -> None

  let of_ast = Constructor_argument.make_of_ast ~of_ast_internal
end

module Expression = struct
  type t =
    | Jexp_comprehension of Comprehensions.expression
    | Jexp_immutable_array of Immutable_arrays.expression
    | Jexp_layout of Layouts.expression
    | Jexp_n_ary_function  of N_ary_functions.expression

  let of_ast_internal (feat : Feature.t) expr = match feat with
    | Language_extension Comprehensions ->
      let expr, attrs = Comprehensions.comprehension_expr_of_expr expr in
      Some (Jexp_comprehension expr, attrs)
    | Language_extension Immutable_arrays ->
      let expr, attrs = Immutable_arrays.of_expr expr in
      Some (Jexp_immutable_array expr, attrs)
    | Language_extension Layouts ->
      let expr, attrs = Layouts.of_expr expr in
      Some (Jexp_layout expr, attrs)
    | Builtin -> begin
        match N_ary_functions.of_expr expr with
        | Some (expr, attrs) -> Some (Jexp_n_ary_function expr, attrs)
        | None -> None
      end
    | _ -> None

  let of_ast = Expression.make_of_ast ~of_ast_internal

  let expr_of ~loc ~attrs t =
    let expr =
      match t with
      | Jexp_comprehension x   -> Comprehensions.expr_of   ~loc x
      | Jexp_immutable_array x -> Immutable_arrays.expr_of ~loc x
      | Jexp_layout x          -> Layouts.expr_of          ~loc x
      | Jexp_n_ary_function  x -> N_ary_functions.expr_of   ~loc x
    in
    (* See Note [Outer attributes at end] *)
    { expr with pexp_attributes = expr.pexp_attributes @ attrs }
end

module Pattern = struct
  type t =
    | Jpat_immutable_array of Immutable_arrays.pattern
    | Jpat_layout of Layouts.pattern

  let of_ast_internal (feat : Feature.t) pat = match feat with
    | Language_extension Immutable_arrays ->
      let expr, attrs = Immutable_arrays.of_pat pat in
      Some (Jpat_immutable_array expr, attrs)
    | Language_extension Layouts ->
      let pat, attrs = Layouts.of_pat pat in
      Some (Jpat_layout pat, attrs)
    | _ -> None

  let of_ast = Pattern.make_of_ast ~of_ast_internal

  let pat_of ~loc ~attrs t =
    let pat =
      match t with
      | Jpat_immutable_array x -> Immutable_arrays.pat_of ~loc x
      | Jpat_layout x -> Layouts.pat_of ~loc x
    in
    (* See Note [Outer attributes at end] *)
    { pat with ppat_attributes = pat.ppat_attributes @ attrs }
end

module Module_type = struct
  type t =
    | Jmty_strengthen of Strengthen.module_type

  let of_ast_internal (feat : Feature.t) mty = match feat with
    | Language_extension Module_strengthening ->
      let mty, attrs = Strengthen.of_mty mty in
      Some (Jmty_strengthen mty, attrs)
    | _ -> None

  let of_ast = Module_type.make_of_ast ~of_ast_internal

  let mty_of ~loc ~attrs t =
    let mty =
      match t with
      | Jmty_strengthen x -> Strengthen.mty_of ~loc x
    in
    (* See Note [Outer attributes at end] *)
    { mty with pmty_attributes = mty.pmty_attributes @ attrs }
end

module Signature_item = struct
  type t =
    | Jsig_include_functor of Include_functor.signature_item

  let of_ast_internal (feat : Feature.t) sigi =
    match feat with
    | Language_extension Include_functor ->
      Some (Jsig_include_functor (Include_functor.of_sig_item sigi))
    | _ -> None

  let of_ast = Signature_item.make_of_ast ~of_ast_internal
end

module Structure_item = struct
  type t =
    | Jstr_include_functor of Include_functor.structure_item

  let of_ast_internal (feat : Feature.t) stri =
    match feat with
    | Language_extension Include_functor ->
      Some (Jstr_include_functor (Include_functor.of_str_item stri))
    | _ -> None

  let of_ast = Structure_item.make_of_ast ~of_ast_internal
end

module Extension_constructor = struct
  type t =
    | Jext_layout of Layouts.extension_constructor

  let of_ast_internal (feat : Feature.t) ext = match feat with
    | Language_extension Layouts ->
      let ext, attrs = Layouts.of_extension_constructor ext in
      Some (Jext_layout ext, attrs)
    | _ -> None

  let of_ast = Extension_constructor.make_of_ast ~of_ast_internal

  let extension_constructor_of ~loc ~name ~attrs ?info ?docs t =
    let ext_ctor =
      match t with
      | Jext_layout lext ->
          Layouts.extension_constructor_of ~loc ~name ?info ?docs lext
    in
    (* See Note [Outer attributes at end] *)
    { ext_ctor with pext_attributes = ext_ctor.pext_attributes @ attrs }
end
