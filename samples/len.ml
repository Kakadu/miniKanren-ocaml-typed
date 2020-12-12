open OCanren

let() = Printexc.record_backtrace true

let (====) a b n st =
  (* Format.printf "unify from line %d\n%!" n; *)
  OCanren.(a === b) st

let mylen1_count = ref 0
let mylen2_count = ref 0

let rec mylen1 xs rez =
  incr mylen1_count;

  let open OCanren.Std in
  conde
  [ fresh (h tl p)
      ((xs ==== (h%tl)) __LINE__)
      ((rez ==== (Nat.succ p)) __LINE__)
      (mylen1 tl p)
  ; fresh ()
      ((xs ==== (nil())) __LINE__)
      ((rez ==== Nat.zero) __LINE__)
  ]

let rec mylen2 xs rez =
  incr mylen2_count;
  let open OCanren.Std in
  conde
  [ fresh (h tl p)
      (xs === h%tl)
      (mylen2 tl p)
      (rez === Nat.succ p)
  ; fresh () (xs === nil()) (rez === Nat.zero)
  ]

(* https://github.com/kajigor/mk-transformers-bench/blob/master/experiments/length/len0.ml *)
let len0 y1 y2 =
  let open OCanren.Std in
  let rec len xs l =
    (((xs === (List.nil ())) &&& (l === Nat.zero)) |||
    (fresh (m t h)
      (((xs === (h % t)) &&&
       ((l === (Nat.succ m)) &&&
       (len t m))))))
  in  (len y1 y2)

(* https://github.com/kajigor/mk-transformers-bench/blob/master/experiments/length/len2.ml *)
let len2 y1 y2 =
  let open OCanren.Std in
  let rec len xs l =
    ( (fresh (m t h)
       (((xs === (h % t)) &&&
         ((len t m) &&&
         (l === (Nat.succ m)))))) |||
      ((xs === (List.nil ())) &&& (l === Nat.zero))
    )
  in  (len y1 y2)



(* ************************************************************ *)



let make_list n : (_,_) injected =
  assert (n>=0);
  let rec helper acc n =
    if n<= 0 then acc
    else helper (Std.List.cons !!1 acc) (n-1)
  in
  helper (Std.nil ()) n

let test ?(occurs=true) rel xs700 expected () =
  let () =
    (if occurs then Runconf.occurs_check_on else Runconf.occurs_check_off) ()
  in
  let s = run q (rel xs700) (fun rr -> rr#prjc (Std.Nat.prjc (fun _ _ -> assert false))) in
  (* assert (not (Stream.is_empty s)); *)
  let nat = Stream.hd s in
  assert (Std.Nat.to_int nat = expected)

let __ () =
  let n = 500 in
  let xs5 = make_list n in

  mylen1_count := 0;
  Format.printf "len 1\n%!";
  test mylen1 xs5 n ();
  let p1 = Stream.(from_fun_counter ()) in
  let b1 = Stream.bind_counter () in
  Format.printf "len 1 finished with %d calls\n%!" !mylen1_count;
  Format.printf "\tfrom_fun_counter = %d\n%!" p1;
  Format.printf "\tbind_counter    = %d\n%!" b1;

  mylen2_count := 0;
  Format.printf "len 2\n%!";
  test mylen2 xs5 n ();
  let p2 = Stream.(from_fun_counter ()) - p1 in
  let b2 = Stream.bind_counter () - b1 in
  Format.printf "len 2 finished with %d calls\n%!" !mylen2_count;
  Format.printf "\tfrom_fun_counter = %d\n%!" p2;
  Format.printf "\tbind_counter    = %d\n%!" b2;
  ()

let () =
  let n = 400 in
  let xs700 = make_list n in

  let open Benchmark  in
  let res = throughputN ~style:Nil ~repeat:2 2
      [
        (* ("test1 occurs=on ", test mylen1 xs700 700, ()); *)
        (* ("test2 occurs=on ", test mylen2 xs700 700, ()); *)
        (* ("mylen1 occurs=off", test ~occurs:false mylen1 xs700 n, ());
        ("mylen2 occurs=off", test ~occurs:false mylen2 xs700 n, ());
        ("len0   occurs=off", test ~occurs:false len0 xs700 n, ());
        ("len2   occurs=off", test ~occurs:false len2 xs700 n, ()); *)
        ("mylen1 occurs=on ", test ~occurs:true mylen1 xs700 n, ());
        ("mylen2 occurs=on ", test ~occurs:true mylen2 xs700 n, ());
        ("len0   occurs=on ", test ~occurs:true len0 xs700 n, ());
        ("len2   occurs=on ", test ~occurs:true len2 xs700 n, ());
      ]
  in
  tabulate res;
  (* Gc.print_stat stdout; *)
  ()




(*

  *)
