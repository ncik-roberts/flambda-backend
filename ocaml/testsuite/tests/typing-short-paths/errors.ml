(* TEST
   flags = " -short-paths "
   * expect
*)

module M = struct type t = T end

type t = M.t

let x : M.t = S
[%%expect {|
module M : sig type t = T end
type t = M.t
Line 5, characters 14-15:
5 | let x : M.t = S
                  ^
Error: This variant expression is expected to have type t
       There is no constructor S within type t
|}]

module M = struct
  class c = object method foo = 3 end
end

type c = M.c

let () = (new M.c)#bar
[%%expect {|
module M : sig class c : object method foo : int end end
type c = M.c
Line 7, characters 9-18:
7 | let () = (new M.c)#bar
             ^^^^^^^^^
Error: This expression has type c
       It has no method bar
|}]

(** Cycle type definitions *)

type 'a t = 'a t
[%%expect {|
Line 3, characters 0-16:
3 | type 'a t = 'a t
    ^^^^^^^^^^^^^^^^
Error: The type abbreviation t is cyclic:
         'a t = 'a t
|}]

type 'a t = 'a u
and 'a u = 'a v * 'a
and 'a v = 'a w list
and 'a w = 'a option z
and 'a z = 'a t
[%%expect {|
Line 1, characters 0-16:
1 | type 'a t = 'a u
    ^^^^^^^^^^^^^^^^
Error: The type abbreviation t is cyclic:
         'a t = 'a u,
         'a u = 'a v * 'a,
         'a v * 'a contains 'a v,
         'a v = 'a w list,
         'a w list contains 'a w,
         'a w = 'a option z,
         'a option z = 'a option t
|}]


type 'a u = < x : 'a>
and 'a t = 'a t u;;
[%%expect{|
Line 2, characters 0-17:
2 | and 'a t = 'a t u;;
    ^^^^^^^^^^^^^^^^^
Error: The type abbreviation t is cyclic:
         'a t u contains 'a t,
         'a t = 'a t u,
         'a t u contains 'a t
|}];; (* fails since 4.04 *)


module rec A : sig type t = B.t -> int end = struct type t = B.t -> int end
       and B : sig type t = A.t end = struct type t = A.t end;;
[%%expect {|
Line 1, characters 0-75:
1 | module rec A : sig type t = B.t -> int end = struct type t = B.t -> int end
    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: The definition of A.t contains a cycle:
         A.t -> int contains A.t,
         A.t = A.t,
         A.t = A.t -> int,
         A.t -> int contains A.t,
         A.t = A.t
|}]
