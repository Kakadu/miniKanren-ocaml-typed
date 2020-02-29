open Printf
open OCanren
open OCanren.Std
open Tester

(* all lists that contain ones *)
let rec ones out =
  conde
    [ List.nullo out
    ; fresh (d)
        ((!!1 % d) === out)
        (ones d)
  ]


let show_int_list   = GT.(show List.ground @@ show int)
let show_intl_llist = GT.(show List.logic @@ show logic @@ show int)

let reifier eta = List.reify OCanren.reify eta
let runL n = runR reifier show_int_list show_intl_llist n

let odds xs =
  (* returns true when constraint is violated *)
  (*  Format.printf "odds constraint called on '%s'\n%!" (show_intl_llist xs);*)
  let rec helper acc = function
  | Var (_,_) -> false
  | Value (Std.List.Cons (_, tl)) -> helper (not acc) tl
  | Value Nil when acc -> true
  | Value Nil          -> false
  in
  helper false xs

let list_of_ones_even_length q = (structural q reifier odds) &&& (ones q)

let _freeVars =
  runL  10   q    qh (REPR(list_of_ones_even_length))

