(* TEST
   * toplevel
   flags = "-extension layouts"
*)

(* CR layouts 1.5: this will stop being a syntax error and start being
   a type-checking error soon.
*)

(* This test makes sure that [type t : unboxed = manifest] doesn't get
   (incorrectly) interpreted as [type t = manifest [@@unboxed]].
 *)

type t : unboxed = { single_field : string }
