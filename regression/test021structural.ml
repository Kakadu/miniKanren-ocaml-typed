open Printf
open OCanren
open OCanren.Std
open Tester

let rec ones out =
  conde
    [ List.nullo out
    ; fresh (d)
        ((!!1 % d) === out)
        (ones d)
  ]


let show_int_list   = GT.(show List.ground @@ show int)
let show_intl_llist = GT.(show List.logic @@ show logic @@ show int)

(*let _ffoo _ =
  run_exn show_int_list (-1)  qr qrh (REPR (fun q r     -> multo q r (build_num 1)                          ));
  run_exn show_int_list (-1)   q  qh (REPR (fun q       -> multo (build_num 7) (build_num 63) q             ));
  run_exn show_int_list (-1)  qr qrh (REPR (fun q r     -> divo (build_num 3) (build_num 2) q r             ));
  run_exn show_int_list (-1)   q  qh (REPR (fun q       -> logo (build_num 14) (build_num 2) (build_num 3) q));
  run_exn show_int_list (-1)   q  qh (REPR (fun q       -> expo (build_num 3) (build_num 5) q               ))*)

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

(*let (_:int) = fortytwo*)

let _freeVars =
  runL  (10)   q    qh (REPR (fun q -> (fortytwo q reifier odds) &&& (ones q)));
  ()
