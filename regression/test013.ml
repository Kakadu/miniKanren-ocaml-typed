open GT
open MiniKanren
open Tester

let show_nat        = Nat.show_ground
let show_bool       = Bool.show_ground
(* let show_nat_list   = show_fancy @@ show(GT.list) (show Nat.ground)
let show_bool_list  = show_fancy @@ show(GT.list) (show Bool.ground)
let show_option_nat = show_fancy @@ show(option)  (show Nat.ground) *)
(* let show_int        = show_fancy @@ string_of_int
let show_int_list   = show_fancy @@ show(GT.list) string_of_int *)

let (?$) = inj_nat
let nats = inj_nat_list
let bools bs = inj_list @@ List.map Bool.inj bs

let unitf : (unit,unit) fancy = MiniKanren.inj @@ lift ()

open Bool
open Nat
open List

let sumo = foldro addo ?$0

let _ =
  run_exn show_nat          1    q (REPR (fun q     -> mulo ?$3 q   ?$6                              ))   qh;
  (* run_exn show_bool         1    q (REPR (fun q     -> noto' Bool.true_  q                                ))   qh;
  run_exn show_bool         1    q (REPR (fun q     -> noto' Bool.false_ q                                ))   qh;
  run_exn show_bool         1    q (REPR (fun q     -> noto' q      Bool.true_                            ))   qh;
  run_exn show_bool         1    q (REPR (fun q     -> oro  Bool.false_ Bool.false_ q                          ))   qh;
  run_exn show_bool         1    q (REPR (fun q     -> oro  Bool.false_ Bool.true_  q                          ))   qh;
  run_exn show_bool         1    q (REPR (fun q     -> oro  Bool.true_  Bool.false_ q                          ))   qh;
  run_exn show_bool         1    q (REPR (fun q     -> oro  Bool.true_  Bool.true_  q                          ))   qh;
  run_exn show_bool         1    q (REPR (fun q     -> ando Bool.false_ Bool.false_ q                          ))   qh;
  run_exn show_bool         1    q (REPR (fun q     -> ando Bool.false_ Bool.true_  q                          ))   qh;
  run_exn show_bool         1    q (REPR (fun q     -> ando Bool.true_  Bool.false_ q                          ))   qh;
  run_exn show_bool         1    q (REPR (fun q     -> ando Bool.true_  Bool.true_  q                          ))   qh;
  run_exn show_nat          1    q (REPR (fun q     -> addo ?$0 ?$1 q                                ))   qh;
  run_exn show_nat          1    q (REPR (fun q     -> addo ?$1 q   ?$3                              ))   qh;
  run_exn show_nat          1    q (REPR (fun q     -> mulo ?$1 ?$2 q                                ))   qh;
  (* hangs *)
  (* run_exn show_nat          1    q (REPR (fun q     -> mulo ?$3 q   ?$6                              ))   qh; *)
  run_exn show_nat          1    q (REPR (fun q     -> mulo ?$3 ?$0 q                                ))   qh;
  run_exn show_nat          1    q (REPR (fun q     -> mulo q   ?$5 ?$0                              ))   qh;
  run_exn show_nat          3    q (REPR (fun q     -> mulo q   ?$0 ?$0                              ))   qh;
  run_exn show_nat          1    q (REPR (fun q     -> sumo (inj_list []) q                          ))   qh;

  run_exn show_nat          1    q (REPR (fun q     -> sumo (nats [3;1;2]) q                         ))   qh;

  run_exn show_nat          1    q (REPR (fun q     -> sumo (?$0 % (?$1 % (q %< ?$3))) ?$6           ))   qh;


  run_exn show_nat          1    q (REPR (fun q     -> lengtho (nats [1;2;3;4]) q                ))   qh;
  run_exn show_nat          1    q (REPR (fun q     -> lengtho (inj_list [unitf; unitf; unitf]) q    ))   qh;
  run_exn show_nat          1    q (REPR (fun q     -> lengtho (bools [false; true]) q               ))   qh;
  run_exn show_nat          1    q (REPR (fun q     -> lengtho (nats [4;3;2;1;0]) q                  ))   qh;
  run_exn show_nat_list     1    q (REPR (fun q     -> lengtho q ?$0                                 ))   qh;
  run_exn show_bool         1    q (REPR (fun q     -> anyo (bools [false;false;true]) q          ))   qh;
  run_exn show_bool         1    q (REPR (fun q     -> anyo (bools [false;false]) q               ))   qh;
  run_exn show_bool         1    q (REPR (fun q     -> allo (bools [true;false;true]) q           ))   qh;
  run_exn show_bool         1    q (REPR (fun q     -> allo (Bool.true_ % (q %< Bool.true_)) Bool.true_             ))   qh;
  run_exn show_bool       (-1) qrs (REPR (fun q r s -> allo (Bool.true_ % (q %< r)) s                     )) qrsh;
  run_exn show_nat_list     1    q (REPR (fun q     -> mapo (addo ?$1) (nats [0;1;2]) q              ))   qh;
  run_exn show_nat_list     1    q (REPR (fun q     -> mapo (addo ?$2) q (nats [4;3;2])              ))   qh;
  run_exn show_nat          1    q (REPR (fun q     -> mapo (addo q) (nats [1;2;3]) (nats [4;5;6])   ))   qh;
  run_exn show_nat          1    q (REPR (fun q     -> mapo (mulo q) (nats [1;2;3]) (nats [2;4;6])   ))   qh;
  run_exn show_nat          1   qr (REPR (fun q r   -> mapo (mulo q) (nats [1;2]) (?$2 %< r)         ))  qrh;
  run_exn show_int_list     1    q (REPR (fun q     -> mapo (===) (nats [1;2;3]) q               ))   qh;
  run_exn show_int          1    q (REPR (fun q     -> mapo (===) (nats [1;2;3]) (?$1 % (?$2 %< q))))   qh;
  run_exn show_bool_list    1    q (REPR (fun q     -> mapo noto' (bools [true;false;true;]) q    ))   qh;
  run_exn show_bool_list    1    q (REPR (fun q     -> mapo noto' (bools []) q                    ))   qh;
  run_exn show_nat_list   (-1)   q (REPR (fun q     -> filtero (eqo ?$2) (nats [0;1;2;3]) q          ))   qh;
  run_exn show_option_nat   1    q (REPR (fun q     -> lookupo (eqo ?$1) (nats [0;2;1;3]) q          ))   qh; *)
  ()

let _freeVars () =
  (* run_exn show_nat          3   qr (REPR (fun q r   -> addo q   r   q                                ))  qrh;
  run_exn show_nat          3   qr (REPR (fun q r   -> mulo q   r   q                                ))  qrh;
  run_exn show_nat_list     1    q (REPR (fun q     -> lengtho q ?$3                                 ))   qh; *)
  ()
