open MiniKanren
open Std
open Tester
open Printf
open GT

let show_int       = show(int)


module P = Presburger.T
let _ =
  let wrap1 g =   run_exn show_int 1  q qh g in
  let open P in
  wrap1 (REPR(fun q -> q === !!5 ));
  wrap1 (REPR(fun q -> (q === !!5) &&& (presburo [ (int 10 <= int 6) ]) ));
  wrap1 (REPR(fun q -> (q === !!5) &&& (presburo [ (!q <= int 6) ]) ));
  wrap1 (REPR(fun q -> (q === !!5) &&& (presburo [ (!q <= int 4) ]) ));
  ()
