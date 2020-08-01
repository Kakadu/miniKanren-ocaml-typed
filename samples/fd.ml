open OCanren
open Tester

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
  runL   1  q     qh (REPR (fun x -> (FD.domain x [1;2]) &&&  (FD.neq x !!1) &&& (FD.neq x !!2) ));
  runL   1  q     qh (REPR (fun x -> (FD.domain x [1;2]) &&&  (FD.neq x !!1) ));
  runL   1  qrst  qrsth (REPR (rel3 [1;2;3]));
  runL   1  qrst  qrsth (REPR (rel3 [1;2;3;4]));
  ()

let make_default n : goal =
  let dom v = Std.Nat.(<) v (Std.nat (n)) in
  let rec make prev_var n =
    if n<=0 then success
    else
      fresh (v)
        (Std.Nat.(<) prev_var v)
        (dom v)
        (make v (n-1))
  in
  fresh (q) (dom q) (make q n)

let make_fd n : goal =
  let dom = List.init n (fun n -> n) in
  let open OCanren in
  let rec make prev_var n =
    if n<=0 then success
    else
      fresh (v)
        (FD.lt prev_var v)
        (FD.domain v dom)
        (make v (n-1))
  in

  let rel = fresh (q) (FD.domain q dom) (make q n) in
  rel

let () =
  let open Benchmark in
  let res =
    let test fd n =
      run q (fun _ -> fd n) (fun rr -> rr#reify OCanren.reify) |> (fun s -> assert (Stream.is_empty s))
    in
    throughputN ~repeat:3 4
      [ ("fd3" , test make_fd, 3)
      ; ("def3", test make_default, 3)
      ]
  in
  print_newline ();
  tabulate res


