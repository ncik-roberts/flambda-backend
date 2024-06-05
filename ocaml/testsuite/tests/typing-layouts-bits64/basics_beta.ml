(* TEST
   {
    flags = "-extension layouts_alpha";
    expect;
   }{
    flags = "-extension layouts_beta";
    expect;
   }
*)

(* We should move these back into [basics.ml] once
   mixed blocks are out of beta. *)

type t_bits64 : bits64
type ('a : bits64) t_bits64_id = 'a

[%%expect{|
type t_bits64 : bits64
type ('a : bits64) t_bits64_id = 'a
|}];;

(****************************************************)
(* Test 5: Allowed in some structures in typedecls. *)

type t5_1 = { x : t_bits64 };;
[%%expect{|
type t5_1 = { x : t_bits64; }
|}];;

type t5_2 = { y : int; x : t_bits64 };;
[%%expect{|
type t5_2 = { y : int; x : t_bits64; }
|}];;

type t5_2' = { y : string; x : t_bits64 };;
[%%expect{|
type t5_2' = { y : string; x : t_bits64; }
|}];;

type t5_4 = A of t_bits64;;
[%%expect{|
type t5_4 = A of t_bits64
|}];;

type t5_5 = A of int * t_bits64;;
[%%expect{|
type t5_5 = A of int * t_bits64
|}];;

type ('a : bits64) t5_7 = A of int
type ('a : bits64) t5_8 = A of 'a;;
[%%expect{|
type ('a : bits64) t5_7 = A of int
type ('a : bits64) t5_8 = A of 'a
|}]

(* not allowed: value in flat suffix *)
type 'a t_disallowed = A of t_bits64 * 'a

[%%expect{|
Line 1, characters 23-41:
1 | type 'a t_disallowed = A of t_bits64 * 'a
                           ^^^^^^^^^^^^^^^^^^
Error: Expected all flat constructor arguments after non-value argument,
       t_bits64, but found boxed argument, 'a.
|}]

(*****************************************************)
(* Test 11: Allow bits64 in some extensible variants *)

(* CR layouts v5.9: Actually allow mixed extensible variant blocks. *)

(* See [basics_alpha.ml] and [basics_beta.ml] for now *)
type t11_1 = ..

type t11_1 += A of t_bits64;;
[%%expect{|
type t11_1 = ..
Line 3, characters 14-27:
3 | type t11_1 += A of t_bits64;;
                  ^^^^^^^^^^^^^
Error: Extensible types can't have fields of unboxed type. Consider wrapping the unboxed fields in a record.
|}]

type t11_1 += B of int64#;;
[%%expect{|
Line 1, characters 14-25:
1 | type t11_1 += B of int64#;;
                  ^^^^^^^^^^^
Error: Extensible types can't have fields of unboxed type. Consider wrapping the unboxed fields in a record.
|}]

type ('a : bits64) t11_2 = ..

type 'a t11_2 += A of int

type 'a t11_2 += B of 'a;;

[%%expect{|
type ('a : bits64) t11_2 = ..
type 'a t11_2 += A of int
Line 5, characters 17-24:
5 | type 'a t11_2 += B of 'a;;
                     ^^^^^^^
Error: Extensible types can't have fields of unboxed type. Consider wrapping the unboxed fields in a record.
|}]

(* not allowed: value in flat suffix *)
type 'a t11_2 += C : 'a * 'b -> 'a t11_2

[%%expect{|
Line 1, characters 17-40:
1 | type 'a t11_2 += C : 'a * 'b -> 'a t11_2
                     ^^^^^^^^^^^^^^^^^^^^^^^
Error: Expected all flat constructor arguments after non-value argument, 'a,
       but found boxed argument, 'b.
|}]
