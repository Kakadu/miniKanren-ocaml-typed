open Printf
open OCanren
open OCanren.Std
open Tester

let long_item =
  let rec helper acc n =
    if n>=100 then acc
    else helper (!!1 % acc) (n+1)
  in
  helper (nil ()) 0

module M = struct
  type ground = int Std.List.ground Std.List.ground
  type logic = int OCanren.logic Std.List.logic Std.List.logic
  type injected = (ground, logic) OCanren.injected

  let reify env x = List.reify (List.reify OCanren.reify) env x
end
let show_ground = GT.(show List.ground @@ (fun _ -> "?"))
let show_logic  = GT.(show List.logic @@ show logic @@ (fun _ -> "?"))

let runL n = runR  M.reify show_ground show_logic n

(* all lists that contain long items *)
let rec lists (out: M.injected) =
  conde
    [ List.nullo out
    ; fresh (d)
        ((long_item % d) === out)
        (lists d)
    ]


let _ =
  runL  10  q  qh (REPR(lists))

let even_parser v =
  let open OCanren.Parser in
  let rec helper n (v: M.injected) =
    (List.Parser.nil v >>= fun () -> return (n mod 2 = 0))
    <|>
    (List.Parser.cons v >>= fun (_,tl) -> helper (n+1) tl)
    <|>
    (var v >>= fun () -> return true)
  in
  helper 0 v

let extra_goal (q: M.injected) =
  let parser2 =
    let open OCanren.Parser in
    even_parser q >>= function true -> return success | false -> return  failure
  in
  fresh ()
    (lists q)
    (goal_of_parser parser2)

let _ =
  runL  10  q  qh (REPR(extra_goal))

let test_structural (q: M.injected) =
  fresh ()
    (structural_parser q even_parser)
    (lists q)

let _ =
  runL  10  q  qh (REPR(test_structural))
