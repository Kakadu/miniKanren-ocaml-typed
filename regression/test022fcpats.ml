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

module ListPatterns : sig
  open Pattern0

  val __ : ('a, 'a -> 'b, 'b) t
  val __any : ('a, 'b, 'b) t
  val nil : ((('a, 'b) Std.List.t, ('c, 'd) List.t logic) injected, 'e, 'e) t
  val cons :
           (('a, 'b) injected, 'c, 'd) Pattern0.t ->
           (('e, 'f) injected, 'd, 'g) Pattern0.t ->
           ((('a, 'e) List.t, ('b, 'f) List.t logic) injected, 'c, 'g) Pattern0.t

end = struct
  open Pattern0

  let __ = Pattern0.__
  let __any = Pattern0.__any

  let nil =
    T
      (fun ctx env (x: (_, _ logic) injected) k ->
        match List.cleanup env x with
        | None ->
            fail env "nil"
        | Some (List.Cons (_,_)) ->
            fail env "nil"
        | Some List.Nil -> incr_matched ctx; k )

  let cons (T fitem) (T ftail) =
    T
      (fun ctx env x k ->
        match List.cleanup env x with
        | None | Some List.Nil -> fail env "cons"
        | Some (List.Cons (item,tail)) ->
            incr_matched ctx;
            k |> fitem  ctx env item  |> ftail ctx env tail)
end


let rec myinvestigate len (q: M.injected) : goal =
  let open ListPatterns in
  apply_fcpm q
    Pattern0.(
        cons __any __ |> map1 ~f:(myinvestigate (len+1))
      |||
        (nil |> map0 ~f:(if len mod 2 = 0 then success else failure))
      ||| (pat_variable |> map0 ~f:success)
      )


let _ =
  runL  10  q  qh (REPR(lists))

let flip f a b = f b a

let list_of_ones_even_length (q: M.injected) =
  fresh ()
    (lists q)
    (myinvestigate 0 q)

let _freeVars =
  runL  10  q  qh (REPR(list_of_ones_even_length))
