open Typedtree
open Types
open Mode

let dummy_layout = Layouts.Layout.value ~why:Type_argument
let dummy_value_mode = Value.legacy
let mkTvar name = Tvar { name; layout = dummy_layout }

let mkTarrow (label, t1, t2, comm) =
  Tarrow ((label, Alloc.legacy, Alloc.legacy), t1, t2, comm)

type texp_ident_identifier = ident_kind * unique_use

let mkTexp_ident ?id:(ident_kind, uu = (Id_value, shared_many_use))
    (path, longident, vd) =
  Texp_ident (path, longident, vd, ident_kind, uu)

type nonrec apply_arg = apply_arg
type texp_apply_identifier = apply_position * Locality.t

let mkTexp_apply ?id:(pos, mode = (Default, Locality.legacy)) (exp, args) =
  Texp_apply (exp, args, pos, mode)

type texp_tuple_identifier = Alloc.t

let mkTexp_tuple ?id:(mode = Alloc.legacy) exps = Texp_tuple (exps, mode)

type texp_construct_identifier = Alloc.t option

let mkTexp_construct ?id:(mode = Some Alloc.legacy) (name, desc, args) =
  Texp_construct (name, desc, args, mode)

type texp_function_param_identifier = {
  param_sort : Layouts.Sort.t;
  param_mode : Alloc.t;
  param_curry : function_curry;
  param_newtypes :
    (string Location.loc * Jane_asttypes.layout_annotation option) list;
}

type texp_function_param = {
  arg_label : Asttypes.arg_label;
  pattern : pattern;
  param : Ident.t;
  partial : partial;
  param_identifier : texp_function_param_identifier;
}

type texp_function_cases_identifier = {
  last_arg_mode : Alloc.t;
  last_arg_sort : Layouts.Sort.t;
  last_arg_exp_extra : exp_extra option;
  last_arg_attributes : attributes;
}

type texp_function_body =
  | Function_body of expression
  | Function_cases of {
      cases : value case list;
      param : Ident.t;
      partial : partial;
      function_cases_identifier : texp_function_cases_identifier;
    }

type texp_function = {
  params : texp_function_param list;
  body : texp_function_body;
}

type texp_function_identifier = {
  alloc_mode : Alloc.t;
  ret_sort : Layouts.Sort.t;
  region : bool;
}

let texp_function_cases_identifier_defaults =
  {
    last_arg_mode = Alloc.legacy;
    last_arg_sort = Layouts.Sort.value;
    last_arg_exp_extra = None;
    last_arg_attributes = [];
  }

let texp_function_param_identifier_defaults =
  {
    param_sort = Layouts.Sort.value;
    param_mode = Alloc.legacy;
    param_curry = More_args { partial_mode = Alloc.legacy };
    param_newtypes = [];
  }

let texp_function_defaults =
  { alloc_mode = Alloc.legacy; ret_sort = Layouts.Sort.value; region = false }

let mkTexp_function ?(id = texp_function_defaults)
    ({ params; body } : texp_function) =
  Texp_function
    {
      params =
        List.map
          (fun { arg_label; pattern; param; partial; param_identifier = id } ->
            {
              fp_arg_label = arg_label;
              fp_kind = Tparam_pat pattern;
              fp_param = param;
              fp_partial = partial;
              fp_sort = id.param_sort;
              fp_mode = id.param_mode;
              fp_curry = id.param_curry;
              fp_newtypes = id.param_newtypes;
              fp_loc = Location.none;
            })
          params;
      body =
        (match body with
        | Function_body expr -> Tfunction_body expr
        | Function_cases
            { cases; param; partial; function_cases_identifier = id } ->
            Tfunction_cases
              {
                fc_cases = cases;
                fc_param = param;
                fc_partial = partial;
                fc_arg_mode = id.last_arg_mode;
                fc_arg_sort = id.last_arg_sort;
                fc_exp_extra = id.last_arg_exp_extra;
                fc_attributes = id.last_arg_attributes;
                fc_loc = Location.none;
              });
      alloc_mode = id.alloc_mode;
      region = id.region;
      ret_sort = id.ret_sort;
    }

type texp_sequence_identifier = Layouts.sort

let mkTexp_sequence ?id:(sort = Layouts.Sort.value) (e1, e2) =
  Texp_sequence (e1, sort, e2)

type texp_match_identifier = Layouts.sort

let mkTexp_match ?id:(sort = Layouts.Sort.value) (e, cases, partial) =
  Texp_match (e, sort, cases, partial)

type matched_expression_desc =
  | Texp_ident of
      Path.t
      * Longident.t Location.loc
      * value_description
      * texp_ident_identifier
  | Texp_apply of
      expression * (Asttypes.arg_label * apply_arg) list * texp_apply_identifier
  | Texp_construct of
      Longident.t Location.loc
      * constructor_description
      * expression list
      * texp_construct_identifier
  | Texp_tuple of expression list * texp_tuple_identifier
  | Texp_function of texp_function * texp_function_identifier
  | Texp_sequence of expression * expression * texp_sequence_identifier
  | Texp_match of
      expression * computation case list * partial * texp_match_identifier
  | O of expression_desc

let view_texp (e : expression_desc) =
  match e with
  | Texp_ident (path, longident, vd, ident_kind, uu) ->
      Texp_ident (path, longident, vd, (ident_kind, uu))
  | Texp_apply (exp, args, pos, mode) -> Texp_apply (exp, args, (pos, mode))
  | Texp_construct (name, desc, args, mode) ->
      Texp_construct (name, desc, args, mode)
  | Texp_tuple (args, mode) -> Texp_tuple (args, mode)
  | Texp_function { params; body; alloc_mode; region; ret_sort } -> (
      let exception Unviewable_function in
      try
        let params =
          List.map
            (fun param ->
              match param.fp_kind with
              | Tparam_optional_default _ -> raise Unviewable_function
              | Tparam_pat pattern ->
                  {
                    arg_label = param.fp_arg_label;
                    param = param.fp_param;
                    partial = param.fp_partial;
                    pattern;
                    param_identifier =
                      {
                        param_sort = param.fp_sort;
                        param_mode = param.fp_mode;
                        param_curry = param.fp_curry;
                        param_newtypes = param.fp_newtypes;
                      };
                  })
            params
        in
        let body =
          match body with
          | Tfunction_body body -> Function_body body
          | Tfunction_cases cases ->
              Function_cases
                {
                  cases = cases.fc_cases;
                  param = cases.fc_param;
                  partial = cases.fc_partial;
                  function_cases_identifier =
                    {
                      last_arg_mode = cases.fc_arg_mode;
                      last_arg_sort = cases.fc_arg_sort;
                      last_arg_exp_extra = cases.fc_exp_extra;
                      last_arg_attributes = cases.fc_attributes;
                    };
                }
        in
        Texp_function ({ params; body }, { alloc_mode; region; ret_sort })
      with Unviewable_function -> O e)
  | Texp_sequence (e1, sort, e2) -> Texp_sequence (e1, e2, sort)
  | Texp_match (e, sort, cases, partial) -> Texp_match (e, cases, partial, sort)
  | _ -> O e

type tpat_var_identifier = Value.t

let mkTpat_var ?id:(mode = dummy_value_mode) (ident, name) =
  Tpat_var (ident, name, mode)

type tpat_alias_identifier = Value.t

let mkTpat_alias ?id:(mode = dummy_value_mode) (p, ident, name) =
  Tpat_alias (p, ident, name, mode)

type tpat_array_identifier = Asttypes.mutable_flag

let mkTpat_array ?id:(mut = Asttypes.Mutable) l = Tpat_array (mut, l)

type 'a matched_pattern_desc =
  | Tpat_var :
      Ident.t * string Location.loc * tpat_var_identifier
      -> value matched_pattern_desc
  | Tpat_alias :
      value general_pattern
      * Ident.t
      * string Location.loc
      * tpat_alias_identifier
      -> value matched_pattern_desc
  | Tpat_array :
      value general_pattern list * tpat_array_identifier
      -> value matched_pattern_desc
  | O : 'a pattern_desc -> 'a matched_pattern_desc

let view_tpat (type a) (p : a pattern_desc) : a matched_pattern_desc =
  match p with
  | Tpat_var (ident, name, mode) -> Tpat_var (ident, name, mode)
  | Tpat_alias (p, ident, name, mode) -> Tpat_alias (p, ident, name, mode)
  | Tpat_array (mut, l) -> Tpat_array (l, mut)
  | _ -> O p

type tstr_eval_identifier = Layouts.sort

let mkTstr_eval ?id:(sort = Layouts.Sort.value) (e, attrs) =
  Tstr_eval (e, sort, attrs)

type matched_structure_item_desc =
  | Tstr_eval of expression * attributes * tstr_eval_identifier
  | O of structure_item_desc

let view_tstr (si : structure_item_desc) =
  match si with
  | Tstr_eval (e, sort, attrs) -> Tstr_eval (e, attrs, sort)
  | _ -> O si

type arg_identifier = Layouts.sort

let mkArg ?id:(sort = Layouts.Sort.value) e = Arg (e, sort)

let map_arg_or_omitted f arg =
  match arg with Arg (e, sort) -> Arg (f e, sort) | Omitted o -> Omitted o

let fold_arg_or_omitted f init arg =
  match arg with Arg (e, sort) -> f init (e, sort) | Omitted _ -> init

let option_of_arg_or_omitted arg =
  match arg with Arg (e, sort) -> Some (e, sort) | Omitted _ -> None

let mk_constructor_description cstr_name =
  {
    cstr_name;
    cstr_res = newty2 ~level:0 (mkTvar (Some "a"));
    cstr_existentials = [];
    cstr_args = [];
    cstr_arity = 0;
    cstr_tag = Ordinary { src_index = 0; runtime_tag = 0 };
    cstr_consts = 0;
    cstr_nonconsts = 0;
    cstr_generalized = false;
    cstr_private = Public;
    cstr_loc = Location.none;
    cstr_attributes = [];
    cstr_inlined = None;
    cstr_uid = Uid.internal_not_actually_unique;
    cstr_arg_layouts = [||];
    cstr_repr = Variant_boxed [||];
    cstr_constant = true;
  }

let mk_value_binding ~vb_pat ~vb_expr ~vb_attributes =
  {
    vb_pat;
    vb_expr;
    vb_attributes;
    vb_loc = Location.none;
    vb_sort = Layouts.Sort.value;
  }

let mkTtyp_any = Ttyp_var (None, None)
let mkTtyp_var s = Ttyp_var (Some s, None)

let is_type_name_used desc typ_name =
  match desc with
  | Ttyp_alias (_, Some s, _) -> s = typ_name
  | Ttyp_constr (_, li, _) -> Longident.last li.txt = typ_name
  | _ -> false
