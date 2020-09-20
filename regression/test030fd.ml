open OCanren
open Tester

let () =
  Format.set_max_indent 0;
  Format.set_margin 100

let runL eta = runR OCanren.reify GT.(show int) GT.(show logic @@ show int) eta

let rel3 dom a b c d =
  fresh (_temp)
    (FD.domain a dom)
    (FD.domain b dom)
    (FD.domain c dom)
    (FD.domain d dom)
    (FD.lt a b)
    (FD.lt b c)
    (FD.lt c d)

let _freeVars =
  runL   1  q     qh (REPR (fun x -> (FD.domain x [1;2]) &&&  (FD.neq x !!2) &&& (FD.neq x !!1) ));
  runL   1  q     qh (REPR (fun x -> (FD.domain x [1;2]) &&&  (FD.neq x !!1) ));
  runL   1  qrst  qrsth (REPR (rel3 [1;2;3]));
  runL   1  qrst  qrsth (REPR (rel3 [1;2;3;4]));
  ()

let _freeVars =
  runL   1  q     qh (REPR (fun x -> (FD.domain x [1;2]) &&&  (x === !!2)  ));
  runL   1  q     qh (REPR (fun x ->  (x === !!2) &&& (FD.domain x [1;2]) ));
  ()
