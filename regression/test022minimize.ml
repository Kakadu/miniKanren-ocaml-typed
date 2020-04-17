open Format

let id x =  x

let make_path (xs: string list) : (string * string) list =
  match xs with
  | [] -> assert false
  | s::nodes ->
      List.rev @@ snd @@
      List.fold_left (fun (prev,acc) x -> (x, (prev,x) :: acc)) (s,[]) nodes

open OCanren
open OCanren.Std
open Tester

@type path = (GT.string * GT.string) Std.List.ground with show
@type path_logic = (GT.string OCanren.logic, GT.string OCanren.logic) Std.Pair.logic Std.List.logic with show
type path_inj = (path, path_logic) OCanren.injected

let path_reifier env x =
  Std.List.reify (Std.Pair.reify OCanren.reify OCanren.reify) env x
let run_path n = runR path_reifier (GT.show path) (GT.show path_logic) n

let rec inject_paths p (rez: path_inj) =
  let rec helper p =
    match p with
    | List.Nil -> (fun rez -> (rez === nil()))
    | List.Cons ((l,r), xs) ->
      (fun rez ->
        fresh (tl)
          (rez === (Std.Pair.pair (!!l) (!!r)) % tl)
          (helper xs tl))
  in
  helper (Std.List.of_list id p) rez

let rec myassoco key xs rez =
  conde
    [ (xs === nil()) &&& failure
    ; fresh (k v tl)
        (xs === (Std.Pair.pair k v) % tl)
        (conde
          [ conde
              [ (k === key) &&& (rez === v)
              ; (k =/= key) &&& failure
              ]
          ; myassoco key tl rez
          ])
    ]

let rec shortest_patho start fin edges rez =
  conde
    [ (start === fin) &&& (rez === nil())
    ; fresh (next tl)
        (myassoco start edges next)
        (rez === (Std.Pair.pair start next) % tl)
        (shortest_patho next fin edges tl)
    ]


let wrap start fin edges q =
  fresh (edgeso)
    (inject_paths edges edgeso)
    (shortest_patho (!!start) (!!fin) edgeso q)

let example0 = make_path [ "start" ]
let example1 = make_path [ "start"; "b"; "c"; "fin" ]
let example2 =
  Stdlib.List.concat
    [ make_path [ "start"; "b1"; "c1"; "d1"; "e1"; "f1"; "fin" ]
    ; make_path [ "start"; "b2"; "c2"; "d2"; "e2";       "fin" ]
    ; make_path [ "start"; "b3"; "c3"; "d3";             "fin" ]
    ; make_path [ "start"; "b4"; "c4";                   "fin" ]
    ; make_path [ "start"; "b5";                         "fin" ]
    ; make_path [ "start";                               "fin" ]
    ]

let _freeVars =
  run_path  (-1)  q  qh (REPR(inject_paths example0));
  run_path  (-1)  q  qh (REPR(inject_paths example1));
  run_path  (-1)  q  qh (REPR(wrap "start" "fin" example1));
  run_path  (-1)  q  qh (REPR(wrap "start" "fin" example2));
  ()


let _freeVars =
  let min start fin examples rez =
    (* get lower bound of size of list *)
    let eval x =
      let rec helper (low,has_fresh) = function
      | Var (_,_) -> (low, true)
      | Value List.Nil -> (low, false)
      | Value (List.Cons (_, tl)) -> helper (low+1,has_fresh) tl
      in
      match helper (0,false) x with
      | n,true -> CAtLeast n
      | n,false -> CFixed n
    in

    minimize eval path_reifier rez (wrap start fin examples)
  in

  run_path  (3)  q  qh (REPR(min "start" "fin" example2));
