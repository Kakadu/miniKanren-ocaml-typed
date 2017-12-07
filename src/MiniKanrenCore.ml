(*
 * MiniKanrenCode: miniKanren implementation.
 * Copyright (C) 2015-2017
 * Dmitri Boulytchev, Dmitry Kosarev, Alexey Syomin, Evgeny Moiseenko
 * St.Petersburg State University, JetBrains Research
 *
 * This software is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Library General Public
 * License version 2, as published by the Free Software Foundation.
 *
 * This software is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 *
 * See the GNU Library General Public License version 2 for more details
 * (enclosed in the file COPYING).
 *)

open Printf

module Log =
  struct

    type t = < name    : string;
               count   : int;
               elapsed : float;
               enter   : unit;
               leave   : unit;
               subs    : t list;
               attach  : t -> unit;
               clear   : unit
             >

    class tc (name : string) =
      object
        val mutable count   = 0
        val mutable elapsed = float_of_int 0
        val mutable origin  = float_of_int 0
        val mutable depth   = 0
        val mutable subs    = ([] : t list)
        method name     = name
        method elapsed  = elapsed
        method count    = count
        method subs     = subs
        method attach l = subs <- l :: subs
        method clear    =
          count   <- 0;
          elapsed <- float_of_int 0;
          depth   <- 0;
          List.iter (fun l -> l#clear) subs
        method enter    =
          count <- count + 1;
          depth <- depth + 1;
          origin <- Unix.((times ()).tms_utime)
        method leave   =
          if depth > 0
          then elapsed <- elapsed +. Unix.((times ()).tms_utime) -. origin
          else failwith (sprintf "OCanren fatal (Log.leave): zero depth");
          depth <- depth - 1
      end

    let create parent name =
      let this = new tc name in
      match parent with
      | Some p -> p#attach this; this
      | None   -> this

    let run   = create None "run"
    let unify = create (Some run) "unify"

    let report () =
      let buf      = Buffer.create 1024      in
      let append s = Buffer.add_string buf s in
      let rec show o l =
        append @@ sprintf "%s%s: count=%d, time=%f\n" o l#name l#count l#elapsed;
        List.iter (show (o ^ "  ")) l#subs
      in
      show "" run;
      Buffer.contents buf

    let clear () = run#clear

  end

let (!!!) = Obj.magic

type w = Unboxed of Obj.t | Boxed of int * int * (int -> Obj.t) | Invalid of int

let is_unboxed t =
  (t = Obj.int_tag || t = Obj.string_tag || t = Obj.double_tag)

let is_boxed t =
  if (t <= Obj.last_non_constant_constructor_tag) &&
     (t >= Obj.first_non_constant_constructor_tag)
  then true
  else false

let is_double_array t =
  t = Obj.double_array_tag

let rec wrap x =
  let t = Obj.tag x in
  if is_boxed t
  then Boxed (t, Obj.size x, Obj.field x)
  else
    if is_unboxed t
    then Unboxed x
    else
      if is_double_array t
      then Boxed (t, Obj.size x, (!!! Obj.double_field) x)
      else
        Invalid t

let copy handler x =
  match wrap x with
  | Unboxed _ -> x
  | Boxed (tag, sx, fx) ->
    let copy = Obj.dup x in
    let sf =
      if tag = Obj.double_array_tag
      then !!!Obj.set_double_field
      else Obj.set_field
    in
    for i = 0 to sx-1 do
      sf copy i @@ !!!(handler !!!(fx i))
    done;
    copy
  | Invalid n -> failwith (sprintf "OCanren fatal (copy): invalid value (%d)" n)

module Stream =
  struct
    type 'a t =
      | Nil
      | Cons of 'a * ('a t)
      | Thunk  of 'a thunk
      | Waiting of 'a suspended list
    and 'a thunk =
      unit -> 'a t
    and 'a suspended =
      {is_ready: unit -> bool; zz: 'a thunk}

    let nil         = Nil
    let single x    = Cons (x, Nil)
    let cons x s    = Cons (x, s)
    let from_fun zz = Thunk zz

    let suspend ~is_ready f = Waiting [{is_ready; zz=f}]

    let rec of_list = function
    | []    -> Nil
    | x::xs -> Cons (x, of_list xs)

    let force = function
    | Thunk zz  -> zz ()
    | xs        -> xs

    let rec mplus xs ys =
      match xs with
      | Nil           -> force ys
      | Cons (x, xs)  -> cons x (from_fun @@ fun () -> mplus (force ys) xs)
      | Thunk   _     -> from_fun (fun () -> mplus (force ys) xs)
      | Waiting ss    ->
        let ys = force ys in
        (* handling waiting streams is tricky *)
        match unwrap_suspended ss, ys with
        (* if [xs] has no ready streams and [ys] is also a waiting stream then we merge them  *)
        | Waiting ss, Waiting ss' -> Waiting (ss @ ss')
        (* if [xs] has no ready streams but [ys] is not a waiting stream then we swap them,
           pushing waiting stream to the back of the new stream *)
        | Waiting ss, _           -> mplus ys @@ from_fun (fun () -> xs)
        (* if [xs] has ready streams then [xs'] contains some lazy stream that is ready to produce new answers *)
        | xs', _ -> mplus xs' ys

    and unwrap_suspended ss =
      let rec find_ready prefix = function
        | ({is_ready; zz} as s)::ss ->
          if is_ready ()
          then Some (from_fun zz), (List.rev prefix) @ ss
          else find_ready (s::prefix) ss
        | [] -> None, List.rev prefix
      in
      match find_ready [] ss with
        | Some s, [] -> s
        | Some s, ss -> mplus (force s) @@ Waiting ss
        | None , ss  -> Waiting ss

    let rec bind s f =
      match s with
      | Nil           -> Nil
      | Cons (x, s)   -> mplus (f x) (from_fun (fun () -> bind (force s) f))
      | Thunk zz      -> from_fun (fun () -> bind (zz ()) f)
      | Waiting ss    ->
        match unwrap_suspended ss with
        | Waiting ss ->
          let helper {zz} as s = {s with zz = fun () -> bind (zz ()) f} in
          Waiting (List.map helper ss)
        | s          -> bind s f

    let rec msplit = function
    | Nil           -> None
    | Cons (x, xs)  -> Some (x, xs)
    | Thunk zz      -> msplit @@ zz ()
    | Waiting ss    ->
      match unwrap_suspended ss with
      | Waiting _ -> None
      | xs        -> msplit xs

    let is_empty s =
      match msplit s with
      | Some _  -> false
      | None    -> true

    let rec map f = function
    | Nil          -> Nil
    | Cons (x, xs) -> Cons (f x, map f xs)
    | Thunk zzz    -> from_fun (fun () -> map f @@ zzz ())
    | Waiting ss   ->
      let helper {zz} as s = {s with zz = fun () -> map f (zz ())} in
      Waiting (List.map helper ss)

    let rec iter f s =
      match msplit s with
      | Some (x, s) -> f x; iter f s
      | None        -> ()

    let rec filter p s =
      match msplit s with
      | Some (x, s) -> let s = filter p s in if p x then Cons (x, s) else s
      | None        -> Nil

    let rec fold f acc s =
      match msplit s with
      | Some (x, s) -> fold f (f acc x) s
      | None        -> acc

    let rec zip xs ys =
      match msplit xs, msplit ys with
      | None,         None          -> Nil
      | Some (x, xs), Some (y, ys)  -> Cons ((x, y), zip xs ys)
      | _                           -> invalid_arg "OCanren fatal (Stream.zip): streams have different lengths"

    let hd s =
      match msplit s with
      | Some (x, _) -> x
      | None        -> invalid_arg "OCanren fatal (Stream.hd): empty stream"

    let tl s =
      match msplit s with
      | Some (_, xs) -> xs
      | None         -> Nil

    let rec retrieve ?(n=(-1)) s =
      if n = 0
      then [], s
      else match msplit s with
      | None          -> [], Nil
      | Some (x, s)  -> let xs, s = retrieve ~n:(n-1) s in x::xs, s

    let take ?n s = fst @@ retrieve ?n s

  end
;;

@type 'a logic =
| Var   of GT.int * 'a logic GT.list
| Value of 'a with show, gmap, html, eq, compare, foldl, foldr

let logic = {logic with
  gcata = ();
  plugins =
    object
      method gmap      = logic.plugins#gmap
      method html      = logic.plugins#html
      method eq        = logic.plugins#eq
      method compare   = logic.plugins#compare
      method foldl     = logic.plugins#foldl
      method foldr     = logic.plugins#foldr
      method show fa x =
        GT.transform(logic)
          (GT.lift fa)
          (object inherit ['a] @logic[show]
             method c_Var _ s i cs =
               let c = match cs with
               | [] -> ""
               | _  -> sprintf " %s" (GT.show(GT.list) (fun l -> "=/= " ^ s.GT.f () l) cs)
               in
               sprintf "_.%d%s" i c
             method c_Value _ _ x = x.GT.fx ()
           end)
          ()
          x
    end
}

module Var =
  struct
    type env    = int
    type scope  = int
    type anchor = int list

    let tabling_env = -1

    let unused_index = -1

    let non_local_scope = -6

    let tabling_scope = -7

    let new_scope =
      let scope = ref 0 in
      fun () -> (incr scope; !scope)

    let global_anchor = [-8]

    type t = {
      anchor        : anchor;
      env           : env;
      index         : int;
      mutable subst : Obj.t option;
      scope         : scope;
      constraints   : Obj.t list
    }

    let make ~env ~scope index = {
      env         = env;
      anchor      = global_anchor;
      subst       = None;
      constraints = [];
      index;
      scope;
    }

    let equal x y =
      assert (x.env = y.env);
      x.index = y.index

    let compare x y =
      assert (x.env = y.env);
      x.index - y.index

    let hash x = Hashtbl.hash x.index

  end

module VarSet = Set.Make(Var)
module VarMap = Map.Make(Var)
module VarTbl = Hashtbl.Make(Var)

type helper = < isVar : 'a . 'a -> bool >

include (struct
type ('a, 'b) injected = 'a
module type T1 =
  sig
    type 'a t
    val fmap : ('a -> 'b) -> 'a t -> 'b t
  end

module type T2 =
  sig
    type ('a, 'b) t
    val fmap : ('a -> 'c) -> ('b -> 'd) -> ('a, 'b) t -> ('c, 'd) t
  end

module type T3 =
  sig
    type ('a, 'b, 'c) t
    val fmap : ('a -> 'q) -> ('b -> 'r) -> ('c -> 's) -> ('a, 'b, 'c) t -> ('q, 'r, 's) t
  end

module type T4 =
  sig
    type ('a, 'b, 'c, 'd) t
    val fmap : ('a -> 'q) -> ('b -> 'r) -> ('c -> 's) -> ('d -> 't) -> ('a, 'b, 'c, 'd) t -> ('q, 'r, 's, 't) t
  end

module type T5 =
  sig
    type ('a, 'b, 'c, 'd, 'e) t
    val fmap : ('a -> 'q) -> ('b -> 'r) -> ('c -> 's) -> ('d -> 't) -> ('e -> 'u) -> ('a, 'b, 'c, 'd, 'e) t -> ('q, 'r, 's, 't, 'u) t
  end

module type T6 =
  sig
    type ('a, 'b, 'c, 'd, 'e, 'f) t
    val fmap : ('a -> 'q) -> ('b -> 'r) -> ('c -> 's) -> ('d -> 't) -> ('e -> 'u) -> ('f -> 'v) -> ('a, 'b, 'c, 'd, 'e, 'f) t -> ('q, 'r, 's, 't, 'u, 'v) t
  end

let to_var (c : helper) x r =
  if c#isVar x
  then
    let x : Var.t = !!!x in
    !!!(Var (x.index, List.map (!!!(r c)) x.Var.constraints))
  else failwith "OCanren fatal (to_var): not a logic variable"

module Fmap (T : T1) =
  struct
    external distrib : ('a,'b) injected T.t -> ('a T.t, 'b T.t) injected = "%identity"

    let rec reify r (c : helper) x =
      if c#isVar x
      then to_var c x (reify r)
      else Value (T.fmap (r c) x)
  end

module Fmap2 (T : T2) =
  struct
    external distrib : (('a,'b) injected, ('c, 'd) injected) T.t -> (('a, 'b) T.t, ('c, 'd) T.t) injected = "%identity"

    let rec reify r1 r2 (c : helper) x =
      if c#isVar x
      then to_var c x (reify r1 r2)
      else Value (T.fmap (r1 c) (r2 c) x)
  end

module Fmap3 (T : T3) =
  struct
    external distrib : (('a, 'b) injected, ('c, 'd) injected, ('e, 'f) injected) T.t -> (('a, 'c, 'e) T.t, ('b, 'd, 'f) T.t) injected = "%identity"

    let rec reify r1 r2 r3 (c : helper) x =
      if c#isVar x then to_var c x (reify r1 r2 r3)
      else Value (T.fmap (r1 c) (r2 c) (r3 c) x)
end

module Fmap4 (T : T4) = struct
  external distrib : (('a,'b) injected, ('c, 'd) injected, ('e, 'f) injected, ('g, 'h) injected) T.t ->
                     (('a, 'c, 'e, 'g) T.t, ('b, 'd, 'f, 'h) T.t) injected = "%identity"

  let rec reify r1 r2 r3 r4 (c : helper) x =
    if c#isVar x
    then to_var c x (reify r1 r2 r3 r4)
    else Value (T.fmap (r1 c) (r2 c) (r3 c) (r4 c) x)
end

module Fmap5 (T : T5) = struct
  external distrib : (('a,'b) injected, ('c, 'd) injected, ('e, 'f) injected, ('g, 'h) injected, ('i, 'j) injected) T.t ->
                     (('a, 'c, 'e, 'g, 'i) T.t, ('b, 'd, 'f, 'h, 'j) T.t) injected = "%identity"

  let rec reify r1 r2 r3 r4 r5 (c : helper) x =
    if c#isVar x
    then to_var c x (reify r1 r2 r3 r4 r5)
    else Value (T.fmap (r1 c) (r2 c) (r3 c) (r4 c) (r5 c) x)
end

module Fmap6 (T : T6) = struct
  external distrib : (('a,'b) injected, ('c, 'd) injected, ('e, 'f) injected, ('g, 'h) injected, ('i, 'j) injected, ('k, 'l) injected) T.t ->
                     (('a, 'c, 'e, 'g, 'i, 'k) T.t, ('b, 'd, 'f, 'h, 'j, 'l) T.t) injected = "%identity"

  let rec reify r1 r2 r3 r4 r5 r6 (c : helper) x =
    if c#isVar x then
    to_var c x (reify r1 r2 r3 r4 r5 r6)
    else Value (T.fmap (r1 c) (r2 c) (r3 c) (r4 c) (r5 c) (r6 c) x)
end

end : sig
  type ('a, 'b) injected

  val to_var: helper -> (('a,'b) injected as 'l) -> (helper -> 'l -> 'b) -> 'b
module type T1 =
  sig
    type 'a t
    val fmap : ('a -> 'b) -> 'a t -> 'b t
  end

module type T2 =
  sig
    type ('a, 'b) t
    val fmap : ('a -> 'c) -> ('b -> 'd) -> ('a, 'b) t -> ('c, 'd) t
  end

module type T3 =
  sig
    type ('a, 'b, 'c) t
    val fmap : ('a -> 'q) -> ('b -> 'r) -> ('c -> 's) -> ('a, 'b, 'c) t -> ('q, 'r, 's) t
  end

module type T4 =
  sig
    type ('a, 'b, 'c, 'd) t
    val fmap : ('a -> 'q) -> ('b -> 'r) -> ('c -> 's) -> ('d -> 't) -> ('a, 'b, 'c, 'd) t -> ('q, 'r, 's, 't) t
  end

module type T5 =
  sig
    type ('a, 'b, 'c, 'd, 'e) t
    val fmap : ('a -> 'q) -> ('b -> 'r) -> ('c -> 's) -> ('d -> 't) -> ('e -> 'u) -> ('a, 'b, 'c, 'd, 'e) t -> ('q, 'r, 's, 't, 'u) t
  end

module type T6 =
  sig
    type ('a, 'b, 'c, 'd, 'e, 'f) t
    val fmap : ('a -> 'q) -> ('b -> 'r) -> ('c -> 's) -> ('d -> 't) -> ('e -> 'u) -> ('f -> 'v) -> ('a, 'b, 'c, 'd, 'e, 'f) t -> ('q, 'r, 's, 't, 'u, 'v) t
  end

module Fmap (T : T1) :
  sig
    val distrib : ('a,'b) injected T.t -> ('a T.t, 'b T.t) injected
    val reify : (helper -> ('a,'b) injected -> 'b) -> helper -> ('a T.t, 'b T.t logic as 'r) injected -> 'r
  end

module Fmap2 (T : T2) :
  sig
    val distrib : (('a,'c) injected, ('b,'d) injected) T.t -> (('a, 'b) T.t, ('c, 'd) T.t) injected
    val reify : (helper -> ('a, 'b) injected -> 'b) -> (helper -> ('c, 'd) injected -> 'd) -> helper -> (('a, 'c) T.t, ('b, 'd) T.t logic as 'r) injected -> 'r
  end

module Fmap3 (T : T3) :
  sig
    val distrib : (('a,'b) injected, ('c, 'd) injected, ('e, 'f) injected) T.t -> (('a, 'c, 'e) T.t, ('b, 'd, 'f) T.t) injected
    val reify : (helper -> ('a, 'b) injected -> 'b) -> (helper -> ('c, 'd) injected -> 'd) -> (helper -> ('e, 'f) injected -> 'f) ->
                helper -> (('a, 'c, 'e) T.t, ('b, 'd, 'f) T.t logic as 'r) injected -> 'r
  end

module Fmap4 (T : T4) :
  sig
    val distrib : (('a,'b) injected, ('c, 'd) injected, ('e, 'f) injected, ('g, 'h) injected) T.t ->
                       (('a, 'c, 'e, 'g) T.t, ('b, 'd, 'f, 'h) T.t) injected

    val reify : (helper -> ('a, 'b) injected -> 'b) -> (helper -> ('c, 'd) injected -> 'd) ->
                (helper -> ('e, 'f) injected -> 'f) -> (helper -> ('g, 'h) injected -> 'h) ->
                helper -> (('a, 'c, 'e, 'g) T.t, ('b, 'd, 'f, 'h) T.t logic as 'r) injected -> 'r
  end

module Fmap5 (T : T5) :
  sig
    val distrib : (('a,'b) injected, ('c, 'd) injected, ('e, 'f) injected, ('g, 'h) injected, ('i, 'j) injected) T.t ->
                       (('a, 'c, 'e, 'g, 'i) T.t, ('b, 'd, 'f, 'h, 'j) T.t) injected

    val reify : (helper -> ('a, 'b) injected -> 'b) -> (helper -> ('c, 'd) injected -> 'd) -> (helper -> ('e, 'f) injected -> 'f) ->
                (helper -> ('g, 'h) injected -> 'h) -> (helper -> ('i, 'j) injected -> 'j) ->
                helper -> (('a, 'c, 'e, 'g, 'i) T.t, ('b, 'd, 'f, 'h, 'j) T.t logic as 'r) injected -> 'r
  end

module Fmap6 (T : T6) :
  sig
    val distrib : (('a,'b) injected, ('c, 'd) injected, ('e, 'f) injected, ('g, 'h) injected, ('i, 'j) injected, ('k, 'l) injected) T.t ->
                       (('a, 'c, 'e, 'g, 'i, 'k) T.t, ('b, 'd, 'f, 'h, 'j, 'l) T.t) injected

    val reify : (helper -> ('a, 'b) injected -> 'b) -> (helper -> ('c, 'd) injected -> 'd) -> (helper -> ('e, 'f) injected -> 'f) ->
                (helper -> ('g, 'h) injected -> 'h) -> (helper -> ('i, 'j) injected -> 'j) -> (helper -> ('k, 'l) injected -> 'l) ->
                helper -> (('a, 'c, 'e, 'g, 'i, 'k) T.t, ('b, 'd, 'f, 'h, 'j, 'l) T.t logic as 'r) injected -> 'r
  end

end)

external lift : 'a -> ('a, 'a) injected                      = "%identity"
external inj  : ('a, 'b) injected -> ('a, 'b logic) injected = "%identity"

let rec reify (c : helper) (n: ('a,'a logic) injected)  =
  if c#isVar n
  then to_var c n reify
  else Value !!!n

exception Not_a_value
exception Occurs_check

let to_logic x = Value x

let from_logic = function
| Value x    -> x
| Var (_, _) -> raise Not_a_value

let (!!) x = inj (lift x)

module Env :
  sig
    type t

    val empty     : unit -> t
    val create    : anchor:Var.env -> t
    val fresh     : (*?name:string ->*) scope:Var.scope -> t -> 'a
    val var       : t -> 'a -> int option
    val is_var    : t -> 'a -> bool
    val free_vars : t -> 'a -> VarSet.t
    val merge     : t -> t -> t
  end =
  struct
    type t = {anchor : Var.env; mutable next : int}

    let last_anchor = ref 11
    let first_var = 10

    let empty () =
      incr last_anchor;
      {anchor = !last_anchor; next = first_var}

    let create ~anchor = {anchor; next = first_var}

    let fresh (*?name *) ~scope e =
      let v = !!!(Var.make ~env:e.anchor ~scope e.next) in
      e.next <- 1 + e.next;
      !!!v

    let var_tag, var_size =
      let index = 0 in (* dummy index *)
      let env   = 0 in (* dummy env token *)
      let scope = 0 in (* dummy scope *)
      let v = Var.make ~env ~scope index in
      Obj.tag !!!v, Obj.size !!!v

    let is_var env x =
      let t = !!! x in
      if Obj.tag  t = var_tag  &&
         Obj.size t = var_size &&
         (let token = (!!!x : Var.t).Var.anchor in (Obj.is_block !!!token) && token == !!!Var.global_anchor)
      then
        let q = (!!!x : Var.t).Var.env in
        if (Obj.is_int !!!q) && q == !!!env.anchor
        then true
        else failwith "OCanren fatal (Env.var): wrong environment"
      else false

    let var env x =
      if is_var env x then Some (!!!x: Var.t).index else None

    let free_vars env x =
      let rec helper fv t =
        if is_var env t
        then VarSet.add (!!!t : Var.t) fv
        else
          match wrap t with
          | Unboxed vx -> fv
          | Boxed (tx, sx, fx) ->
            let rec inner fv i =
              if i < sx
              then inner (helper fv !!!(fx i)) (i+1)
              else fv
            in
            inner fv 0
          | Invalid n -> failwith (sprintf "OCanren fatal (Env.free_vars): invalid value (%d)" n)
      in
      helper VarSet.empty (Obj.repr x)

    let merge {anchor=anchor1; next=next1} {anchor=anchor2; next=next2} =
      assert (anchor1 == anchor2);
      {anchor=anchor1; next = max next1 next2}
  end

module Subst :
  sig
    type t
    type content = {var : Var.t; term : Obj.t }

    val empty : t

    val of_list : content list -> t

    val split : t -> content list

    val walk  : Env.t -> t -> 'a -> 'a

    (* [project env subst x] - performs a deepwalk of term [x],
     *   replacing every variable to relevant binding in [subst];
     *   i.e. it obtains a value of term [x] in [subst] *)
    val project : Env.t -> t -> 'a -> 'a

    (* [refresh ?mapping ~scope dst_env src_env subst x] - takes a term [x],
     *   projects [subst] into it
     *   and replaces all stayed free variables
     *   into fresh variables in destination environment [dst_env].
     *   Returns a modified term along with a mapping from variables in [src_env] into [dst_env].
     *   Takes an optional argumet [mapping], in case it is passed a variable from [src_env]
     *   first is looked up in [mapping] and only if it is not present there
     *   fresh variable from [dst_env] is allocated.
     *)
    val refresh : ?mapping : Var.t VarTbl.t -> scope:Var.scope -> Env.t -> Env.t -> t -> 'a -> Var.t VarTbl.t * 'a

    (* [is_bound x subst] - checks whether [x] is bound by [subst] *)
    val is_bound : Var.t -> t -> bool

    (* [free_vars env subst x] - returns all free-variables of term [x] *)
    val free_vars : Env.t -> t -> 'a -> VarSet.t

    (* [unify env x y scope subst] returns None if two terms are not unifiable.
     *   Otherwise it returns a pair of prefix and new substituion.
     *   Prefix is a list of pairs (var, term) that were added to the original substituion.
     *)
    val unify : scope:Var.scope -> Env.t -> t -> 'a -> 'a -> (content list * t) option

    (* [merge env s1 s2] merges two substituions *)
    val merge : Env.t -> t -> t -> t option

    (* [is_subsumed env s1 s2] checks that s1 is subsumed by s2 (i.e. s2 is more general than s1) *)
    val is_subsumed : Env.t -> t -> t -> bool
  end =
  struct
    type content = {var : Var.t; term : Obj.t }

    type t       = Obj.t VarMap.t

    let empty = VarMap.empty

    let of_list =
      ListLabels.fold_left ~init:empty ~f:(fun subst cnt ->
        VarMap.add cnt.var cnt.term subst
      )

    let split s = VarMap.fold (fun var term xs -> {var; term}::xs) s []

    let rec walk env subst t =
      if Env.is_var env t
      then
        let v = (!!!t : Var.t) in
        match v.subst with
        | Some term -> walk env subst !!!term
        | None ->
            try walk env subst (Obj.obj (VarMap.find v subst))
            with Not_found -> t
      else t

    let rec project env subst x =
      let var = walk env subst x in
      match Env.var env var with
      | None    -> !!!(copy (project env subst) @@ Obj.repr var)
      | Some n  -> var

    let refresh ?(mapping = VarTbl.create 31) ~scope dst_env src_env subst x =
      let rec helper t =
        match Env.var src_env t with
        | None    -> copy helper (Obj.repr t)
        | Some n  ->
          let var = (!!!t : Var.t) in
          try
            Obj.repr @@ VarTbl.find mapping var
          with Not_found ->
            let new_var = Env.fresh ~scope dst_env in
            VarTbl.add mapping var !!!new_var;
            Obj.repr @@ new_var
      in
      (mapping, !!!(helper @@ project src_env subst x))

    let free_vars env subst x =
      Env.free_vars env @@ project env subst x

    let is_bound = VarMap.mem

    let rec occurs env var term subst =
      let y = walk env subst term in
      match Env.var env y with
      | Some yi -> var.Var.index = yi
      | None ->
         match wrap (Obj.repr y) with
         | Unboxed _ -> false
         | Boxed (_, s, f) ->
           let rec inner s f i =
            if i >= s then false
            else occurs env var (!!!(f i)) subst || inner s f (i+1)
           in
           inner s f 0
         | Invalid n when n = Obj.closure_tag -> false
         | Invalid n -> failwith (sprintf "OCanren fatal (Subst.occurs): invalid value (%d)" n)

    let extend ~scope env var term subst =
      if occurs env var term subst then raise Occurs_check
      else
        assert (Env.var env var <> Env.var env term);
        (* It is safe to modify variables destructively if the case of scopes match.
         * There are two cases:
         * 1) If we do unification just after a conde, then the scope is already incremented and nothing goes into
         *    the fresh variables.
         * 2) If we do unification after a fresh, then in case of failure it doesn't matter if
         *    the variable is be distructively substituted: we will not look on it in future.
         *)
        if scope = var.Var.scope
        then begin
          var.subst <- Some (Obj.repr term);
          subst
        end
          else VarMap.add var (Obj.repr term) subst

    let unify ~scope env subst x y =

      (* The idea is to do the unification and collect the unification prefix during the process *)
      let extend var term (prefix, subst) =
        let var = (!!!var: Var.t) in
        let subst = extend ~scope env var term subst in
        ({var; term = Obj.repr term}::prefix, subst)
      in
      let rec helper x y : (content list * t) option -> _ = function
        | None -> None
        | Some ((_, subst) as pair) as acc ->
            let x = walk env subst x in
            let y = walk env subst y in
            match Env.var env x, Env.var env y with
            | (Some xi, Some yi) when xi = yi -> acc
            | Some xi, _        -> Some (extend x y pair)
            | _      , Some yi  -> Some (extend y x pair)
            | _ ->
                let wx, wy = wrap (Obj.repr x), wrap (Obj.repr y) in
                (match wx, wy with
                 | Unboxed vx, Unboxed vy -> if vx = vy then acc else None
                 | Boxed (tx, sx, fx), Boxed (ty, sy, fy) ->
                    if tx = ty && sx = sy
                    then
                      let rec inner i = function
                        | None -> None
                        | res ->
                          if i < sx
                          then inner (i+1) (helper (!!!(fx i)) (!!!(fy i)) res)
                          else res
                      in
                      inner 0 acc
                    else None
                 | Invalid n, _
                 | _, Invalid n -> failwith (sprintf "OCanren fatal (Subst.unify): invalid value (%d)" n)
                 | _ -> None
                )
      in
      try helper !!!x !!!y (Some ([], subst))
      with Occurs_check -> None

      let merge env subst1 subst2 = VarMap.fold (fun var term -> function
        | Some s  -> begin
          match unify ~scope:Var.non_local_scope env s !!!var term with
          | Some (_, s') -> Some s'
          | None         -> None
          end
        | None    -> None
      ) subst1 (Some subst2)

      let is_subsumed env subst =
        VarMap.for_all (fun var term ->
          match unify ~scope:Var.non_local_scope env subst !!!var term with
          | None          -> false
          | Some ([], _)  -> true
          | _             -> false
        )

  end

module Int = struct type t = int let compare = (-) end
module M = Map.Make(Int)

exception Disequality_violated
exception Disequality_fulfilled

module Disequality :
  sig
    (* Efficient representation for storing and updating disequalities during search *)
    type t

    (* Simple representation of disequalities as a formula in Conjunctive Normal Form *)
    type cnf

    (* Simple representation of disequalities as a formula in Disjunctive Normal Form *)
    type dnf

    val empty  : t

    (* [of_disj env subst] build a disequality constraint store from a list of bindings
     *   Ex. [(x, 5); (y, 6)] --> (x =/= 5) \/ (y =/= 6)
     *)
    val of_disj : Env.t -> Subst.content list -> t

    (* [of_conj env subst] build a disequality constraint store from a list of bindings
     *   Ex. [(x, 5); (y, 6)] --> (x =/= 5) /\ (y =/= 6)
     *)
    val of_conj : Env.t -> Subst.content list -> t

    (* [to_cnf env subst diseq] - returns new disequality in cnf representation *)
    val to_cnf : Env.t -> Subst.t -> t -> cnf

    (* [of_cnf env diseq] - builds efficient representation of disequalities from cnf representation *)
    val of_cnf : Env.t -> cnf -> t

    (* [normalize diseq] - normalizes disequalities in cnf representation,
     *   i.e. sorts them such that equal disequalities can be compared by simple equivalence check.
     *   Note that additional measures should be performed in order to do alpha-equivalence check of disequalities.
     *)
    val normalize : cnf -> cnf

    (* [cnf_to_dnf diseq] - converts disequalities in cnf representation to dnf representation *)
    val cnf_to_dnf : cnf -> dnf

    (* [of_dnf env diseq] - converts disequalities in dnf representation into a list of
     *   disequalities in efficient representation.
     *   Semantically the result list is a list of disequalities bound by disjunction.
     *)
    val of_dnf : Env.t -> dnf -> t list

    (* [check ~prefix env subst diseq] - checks that disequality is not violated in refined substitution.
     *   [prefix] is a substitution prefix, i.e. new bindings obtained during unification.
     *   This function may rebuild internal representation of constraints and thus it returns new object.
     *   Raises [Disequality_violated].
     *)
    val check : prefix:Subst.content list -> Env.t -> Subst.t -> t -> t

    (* [extend ~prefix env diseq] - extends disequality with new bindings.
     *   New bindings are interpreted as formula in DNF.
     *   Ex. [(x, 5); (y, 6)] --> (x =/= 5) \/ (y =/= 6)
     *)
    val extend : prefix:Subst.content list -> Env.t -> t -> t

    (* [merge env diseq1 diseq2] - merges two disequality stores *)
    val merge : Env.t -> t -> t -> t

    val reify : Env.t -> Subst.t -> t -> Var.t -> 'a list

    (* [project env subst diseq fv] - projects [diseq] into the set of free-variables [fv],
     *   i.e. it extracts only those constraints that mention at least one variable from [fv]
     *)
    val project : Env.t -> Subst.t -> cnf -> VarSet.t -> cnf

    (* [refresh ?mapping ~scope dst_env src_env subst diseq fv] - takes a disequality store [diseq]
     *   and replaces all free variables into fresh variables in destination environment.
     *   Returns a modified disequality store along with a mapping from variables in [src_env] into [dst_env].
     *   Takes an optional argumet [mapping], in case it is passed a variable from [src_env]
     *   first is looked up in [mapping] and only if it is not present there
     *   fresh variable from [dst_env] is allocated.
     *)
    val refresh : ?mapping: Var.t VarTbl.t -> scope:Var.scope -> Env.t -> Env.t -> Subst.t -> cnf -> Var.t VarTbl.t * cnf
  end =
  struct
    (* Disequality constraints are represented as formula in CNF
     * where each atom is single disequality
     * (i.g. ({x =/= t} \/ {y =/= u}) /\ ({y =/= v} \/ {z =/= w}))
     *
     * Optimisation:
     * For each disjunct in the formula we choose one `sample` (i.e single disequality {x =/= t}).
     * Whenever we want to check the whole disequality constraint we
     * can check single `sample` from each conjunct.
     * If `sample` check is passed (i.e {x =/= t} holds in current substitution) we can
     * skip checks of other disjuncts in this conjunct.
     * Also note that after unification of two terms we can
     * check only those disequalities that involves changed variables.
     * Because of that we maintain an index - a map from variable index to
     * list of conjuncts for which this variable is a `sample`.
     * When `sample` check fails, we change index.
     * We choose another `sample` {y =/= u} and add binding to the map for variable {y}.
     * There is no need to check previous samples in the future (because its assumption is already broken in current substitution)
    *)

    module Disjunction :
      sig
        (* Disjunction.t is a set of single disequalities joint by disjunction *)
        type t

        (* [of_list diseqs] build single disjunction from list of disequalities *)
        val of_list : Subst.content list -> t

        (* [check env subst disj] - checks that disjunction of disequalities is
         *   not violated in (current) substitution.
         *   This function is designed to incrementally refine disequalities
         *   with a series of more and more specialized substitutions.
         *   If arbitary substitutions are passed the result may be invalid.
             *)
        val check : Env.t -> Subst.t -> t -> t

        (* [refine env subst disj] - returns `disequality` prefix along with substitution specialized with that prefix.
         *   It is used in two cases:
         *   1) When we want to `negate` a state of search we try to unify current substitution with disequalities.
         *        If unification succeeds we obtain a new specialized state - a counterexample.
         *        Otherwise the substitution with disequalities forms a tautology and we can skip them.
         *   2) When we want to reify an answer we again try to unify current substitution with disequalities.
         *        Then we look into `disequality` prefix for bindings that should not be met.
         *)
        val refine : Env.t -> Subst.t -> t -> (Subst.content list * Subst.t) option

        (* returns an index of variable involved in some disequality inside disjunction *)
        val index : t -> int

        val reify : Var.t -> t -> 'a
      end =
      struct
        type t = { sample : Subst.content; unchecked : Subst.content list }

        let choose_sample unchecked =
          assert (unchecked <> []);
          { sample = List.hd unchecked; unchecked = List.tl unchecked; }

        (* TODO check that list is valid substitution
           (i.e. no different disequalities for same variable. Example: (x =/= 1) || (x =/= 2) is invalid) *)
        let of_list = choose_sample

        type status =
          | Fulfiled
          | Violated
          | Refined of Subst.content list * Subst.t

        let refine' env subst =
        let open Subst in fun { var; term } ->
          match unify ~scope:Var.non_local_scope env subst !!!var term with
          | None                  -> Fulfiled
          | Some ([], _)          -> Violated
          | Some (prefix, subst)  -> Refined (prefix, subst)

        let rec check env subst {sample; unchecked} =
          match refine' env subst sample with
          | Fulfiled            -> raise Disequality_fulfilled
          | Refined (delta, _)  -> choose_sample (delta @ unchecked)
          | Violated            ->
            match unchecked with
            | [] -> raise Disequality_violated
            | ds -> check env subst @@ choose_sample ds

        let refine env subst {sample; unchecked} =
          let result = ListLabels.fold_left (sample::unchecked) ~init:(Some ([], subst))
                ~f:(fun acc diseq -> match acc with
                    | None -> None
                    | Some (delta, subst) ->
                      match refine' env subst diseq with
                      | Fulfiled                  -> None
                      | Violated                  -> acc
                      | Refined (delta', subst')  -> Some (delta'@delta, subst')
                )
            in
            (* We should not get empty substituion delta here,
             * because it would mean that disequality is violated.
             * But we had to detect violations during search via `check`. *)
            assert (match result with Some ([], _) -> false | _ -> true);
            result

        let reify var {sample; unchecked} =
          if unchecked <> []
          then invalid_arg "OCanren fatal (Disequality.reify): attempting to reify unnormalized disequalities"
          else
            assert (var.Var.index = sample.Subst.var.Var.index);
            !!!(sample.Subst.term)

        let index {sample} = sample.Subst.var.index
      end

    module Index :
      sig
        type t

        val empty     : t
        val is_empty  : t -> bool
        val add       : int -> Disjunction.t -> t -> t
        val get       : int -> t -> Disjunction.t list
        val replace   : int -> Disjunction.t list -> t -> t
        val fold      : ('a -> Disjunction.t -> 'a) -> 'a -> t -> 'a
        val merge     : t -> t -> t
      end =
      struct
        type t = Disjunction.t list M.t

        let empty           = M.empty
        let is_empty        = M.is_empty
        let get k m         = try M.find k m with Not_found -> []
        let add k v m       = M.add k (v::get k m) m
        let replace k vs m  = M.add k vs (M.remove k m)
        let fold f acc m    = M.fold (fun _ disjs acc -> ListLabels.fold_left ~init:acc ~f disjs) m acc
        let merge           = M.union (fun _ d1 d2-> Some (d1 @ d2))
      end

    type t = Index.t

    type cnf = Subst.content list list

    type dnf = Subst.content list list

    let empty = Index.empty

    let extend ~prefix env cstore =
      if prefix=[]
      then cstore
      else
        let disj = Disjunction.of_list prefix in
        Index.add (Disjunction.index disj) disj cstore

    let of_disj env disjs =
      extend ~prefix:disjs env empty

    let of_conj env conjs =
      ListLabels.fold_left conjs ~init:empty
        ~f:(fun acc pair -> extend ~prefix:[pair] env acc)

    let check ~prefix env subst cstore =
      let revisit_conjuncts var_idx conj =
        ListLabels.fold_left conj
            ~init:([], [])
            ~f:(fun (stayed, rebound) disj ->
              try
                let disj = Disjunction.check env subst disj in
                if var_idx = (Disjunction.index disj)
                then (disj::stayed, rebound)
                else (stayed, disj::rebound)
              with Disequality_fulfilled -> (stayed, rebound)
            )
      in
      if Index.is_empty cstore then cstore
      else
      ListLabels.fold_left prefix ~init:cstore
        ~f:(fun cstore cnt ->
          let var_idx = cnt.Subst.var.Var.index in
          let conj = Index.get var_idx cstore in
          let stayed1, rebound1 = revisit_conjuncts var_idx conj in
          let cstore, rebound2 = match Env.var env cnt.Subst.term with
            | Some n ->
              let stayed2, rebound2 = revisit_conjuncts n @@ Index.get n cstore in
              Index.replace n stayed2 cstore, rebound2
            | None   -> cstore, []
          in
          let cstore = Index.replace var_idx stayed1 cstore in
          let extend rebound cstore =
            ListLabels.fold_left rebound ~init:cstore
            ~f:(fun cstore disj ->
              Index.add (Disjunction.index disj) disj cstore
            )
          in
          let cstore = extend rebound1 cstore in
          let cstore = extend rebound2 cstore in
          cstore
        )

    let reify env subst t var =
      let conjs = Index.get var.Var.index t in
      List.map (Disjunction.reify var) conjs

    let merge env = Index.merge

    let to_cnf env subst t =
      Index.fold (fun acc disj ->
        match Disjunction.refine env subst disj with
        | None -> acc
        | Some (delta, _) -> delta::acc
      ) [] t

    let of_cnf env cs =
      ListLabels.fold_left cs ~init:empty ~f:(
        fun acc disj -> extend ~prefix:disj env acc
      )

    let normalize cnf =
      let compare_bindings =
        let open Subst in fun {var=v1; term=t1} {var=v2; term=t2} ->
        if Var.equal v1 v2 then
          compare t1 t2
        else
          Var.compare v1 v2
      in
      let compare_disj ds1 ds2 =
        let rec helper ds1 ds2 =
          match ds1, ds2 with
          | [], [] -> 0
          | (d1::ds1), (d2::ds2) ->
            let res = compare_bindings d1 d2 in
            if res <> 0 then res else helper ds1 ds2
        in
        let l1, l2 = List.length ds1, List.length ds2 in
        let res = compare l1 l2 in
        if res <> 0 then res else helper ds1 ds2
      in
      let sort_disj = List.sort compare_bindings in
      List.sort compare_disj @@ List.map sort_disj cnf

    let cnf_to_dnf =
      ListLabels.fold_left ~init:[[]]
        ~f:(fun acc disj ->
          ListLabels.map acc ~f:(fun conj ->
            let disj = List.filter (fun x -> not @@ List.exists ((=) x) conj) disj in
            List.map (fun x -> x::conj) disj
          ) |> List.concat
        )

    let of_dnf env = List.map (of_conj env)

    let project env subst cs fv =
      (* fixpoint-like computation of disequalities relevant to variables in [fv] *)
      let rec helper fv =
        let open Subst in
        let is_relevant fv {var; term} =
          (VarSet.mem var fv) ||
          (match Env.var env term with Some _ -> VarSet.mem (!!!term) fv | None -> false)
        in
        (* left those disjuncts that contains binding only for variables from [fv] *)
        let cs' = ListLabels.fold_left cs ~init:[]
          ~f:(fun acc disj ->
            if List.for_all (is_relevant fv) disj then
              disj::acc
            else
              acc
          )
        in
        (* obtain a set of free variables from terms mentioned in disequalities *)
        let fv' = ListLabels.fold_left cs' ~init:fv ~f:(fun acc disj ->
          ListLabels.fold_left disj ~init:acc ~f:(fun acc {var; term} ->
            VarSet.union acc @@ Subst.free_vars env subst term
          )
        ) in
        if VarSet.equal fv fv'
        then cs'
        else helper fv'
      in
      let remove_subsumed cs =
        ListLabels.fold_left cs ~init:[] ~f:(fun acc disj ->
          let subst = Subst.of_list disj in
          let is_subsumed = ListLabels.exists acc
            ~f:(fun _,subst' -> Subst.is_subsumed env subst subst')
          in
          if is_subsumed
          then acc
          else
            let acc = ListLabels.filter acc
              ~f:(fun _,subst' -> not @@ Subst.is_subsumed env subst' subst)
            in
            (disj, subst)::acc
        ) |> List.map fst
      in
      remove_subsumed @@ helper fv

    let refresh ?(mapping = VarTbl.create 31) ~scope dst_env src_env subst cs =
      let refresh_binding =
        let open Subst in fun {var; term} ->
        let new_var =
          try
            VarTbl.find mapping var
          with Not_found ->
            let new_var = Env.fresh ~scope dst_env in
            VarTbl.add mapping var new_var;
            new_var
        in
        {var = new_var; term = snd @@ Subst.refresh ~mapping ~scope dst_env src_env subst term}
      in
      let cs' = List.map (List.map refresh_binding) cs in
      (mapping, cs')
end

module State =
  struct
    type t =
      { env   : Env.t
      ; subst : Subst.t
      ; ctrs  : Disequality.t
      ; scope : Var.scope
      }

    let empty () =
      { env   = Env.empty ()
      ; subst = Subst.empty
      ; ctrs  = Disequality.empty
      ; scope = Var.new_scope ()
      }

    let env   {env} = env
    let subst {subst} = subst
    let constraints {ctrs} = ctrs
    let scope {scope} = scope

    let new_var {env; scope} =
      let x = Env.fresh ~scope env in
      let i = (!!!x : Var.t).Var.index in
      (x,i)

    let incr_scope st = {st with scope = Var.new_scope ()}

    let unify x y ({env; subst; ctrs; scope} as st) =
      LOG[perf] (Log.unify#enter);
      let result =
        match Subst.unify ~scope env subst x y with
        | None -> None
        | Some (prefix, s) ->
          try
            let ctrs' = Disequality.check ~prefix env s ctrs in
            Some {st with subst=s; ctrs=ctrs'}
          with Disequality_violated -> None
      in
      LOG[perf] (Log.unify#leave);
      result

    let disunify x y ({env; subst; ctrs; scope} as st) =
      match Subst.unify ~scope:Var.non_local_scope env subst x y with
      | None         -> Some st
      | Some ([], _) -> None
      | Some (prefix, _) ->
          let ctrs' = Disequality.extend ~prefix env ctrs in
          Some {st with ctrs=ctrs'}

    let merge
      {env=env1; subst=subst1; ctrs=ctrs1; scope=scope1}
      {env=env2; subst=subst2; ctrs=ctrs2; scope=scope2} =
      let env = Env.merge env1 env2 in
      match Subst.merge env subst1 subst2 with
      | None       -> None
      | Some subst -> Some
        { env; subst
        ; ctrs  = Disequality.merge env ctrs1 ctrs2
        ; scope = Var.new_scope ()
        }

    let project ({env; subst; ctrs} as st) x =
      let cs = Disequality.to_cnf env subst ctrs in
      let cs = Disequality.project env subst cs @@ Subst.free_vars env subst x in
      {st with ctrs = Disequality.of_cnf env cs}

    let normalize ({env; subst; ctrs; scope} as st) x =
      let cs = Disequality.to_cnf env subst ctrs in
      let cs = Disequality.project env subst cs @@ Subst.free_vars env subst x in
      match Disequality.of_dnf env @@ Disequality.cnf_to_dnf cs with
      | [] -> [{st with ctrs=Disequality.empty}]
      | cs -> List.map (fun ctrs -> {env; subst; ctrs; scope}) cs

    let reify {env; subst; ctrs} x =
      let rec helper forbidden t =
        let var = Subst.walk env subst t in
        match Env.var env var with
        | None -> copy (helper forbidden) (Obj.repr var)
        | Some n when List.mem n forbidden -> Obj.repr var
        | Some n ->
            let cs =
              Disequality.reify env subst ctrs !!!var |>
              List.filter (fun t ->
                match Env.var env t with
                | Some i  -> not (List.mem i forbidden)
                | None    -> true
              ) |>
              List.map (fun t -> !!!(helper (n::forbidden) t))
            in
            Obj.repr {!!!var with Var.constraints = cs}
      in
      !!!(helper [] x)

  end

type 'a goal' = State.t -> 'a

type goal = State.t Stream.t goal'

let success st = Stream.single st
let failure _  = Stream.nil

let call_fresh f =
  let open State in fun ({env; scope} as st) ->
  let x = Env.fresh ~scope env in
  f x st

let (===) x y st =
  match State.unify x y st with
  | None   -> Stream.nil
  | Some s -> Stream.single s

let (=/=) x y st =
  match State.disunify x y st with
  | None   -> Stream.nil
  | Some s -> Stream.single s

let delay g st = Stream.from_fun (fun () -> g () st)

let conj f g st = Stream.bind (f st) g
let (&&&) = conj
let (?&) gs = List.fold_right (&&&) gs success

let disj_base f g st = Stream.mplus (f st) (Stream.from_fun (fun () -> g st))

let disj f g st = let st = State.incr_scope st in disj_base f g |> (fun g -> Stream.from_fun (fun () -> g st))

let (|||) = disj

let (?|) gs st =
  let st = State.incr_scope st in
  let rec inner = function
  | [g]   -> g
  | g::gs -> disj_base g (inner gs)
  | [] -> failwith "Wrong argument of (?!)"
  in
  inner gs |> (fun g -> Stream.from_fun (fun () -> g st))

let conde = (?|)

module Fresh =
  struct
    let succ prev f = call_fresh (fun x -> prev (f x))

    let zero  f = f
    let one   f = succ zero f
    let two   f = succ one f

    (* N.B. Manual inlining of numerals will speed-up OCanren a bit (mainly because of less memory consumption) *)
    (* let two   g = fun st ->
      let scope = State.scope st in
      let env = State.env st in
      let q = Env.fresh ~scope env in
      let r = Env.fresh ~scope env in
      g q r st *)

    let three f = succ two f
    let four  f = succ three f
    let five  f = succ four f

    let q     = one
    let qr    = two
    let qrs   = three
    let qrst  = four
    let pqrst = five
  end

exception FreeVarFound

let has_free_vars is_var x =
  let rec walk x =
    if is_var x then raise FreeVarFound
    else
      match wrap (Obj.repr x) with
      | Boxed (_tag, size, f) ->
        for i = 0 to size - 1 do
          walk (!!!(f i))
        done
      | _ -> ()
  in
  try walk x; false
  with FreeVarFound -> true

let helper_of_state st =
  !!!(object method isVar x = Env.is_var (State.env st) (Obj.repr x) end)

class type ['a,'b] reified = object
  method is_open : bool
  method prj     : 'a
  method reify   : (helper -> ('a, 'b) injected -> 'b) -> 'b
end

let make_rr : ('a, 'b) injected -> State.t -> ('a, 'b) reified =
  let open State in fun x ({env; subst; ctrs;} as st) ->
  let ans = !!!(State.reify st (Obj.repr x)) in
  let is_open = has_free_vars (Env.is_var env) (Obj.repr ans) in
  let c: helper = helper_of_state st in
  object (self)
    method is_open            = is_open
    method prj                = if self#is_open then raise Not_a_value else !!!ans
    method reify reifier      = reifier c ans
  end

let prj x = let rr = make_rr x @@ State.empty () in rr#prj

module ExtractDeepest =
  struct
    let ext2 x = x

    let succ prev (a, z) =
      let foo, base = prev z in
      ((a, foo), base)
  end

module R :
  sig
    val apply_reifier : State.t Stream.t -> ('a, 'b) injected -> ('a, 'b) reified Stream.t
  end =
  struct
    let apply_reifier stream x = Stream.map (make_rr x) stream
  end

module ApplyTuple =
  struct
    let one arg r = R.apply_reifier arg r
    let succ prev = fun arg (r, y) -> (R.apply_reifier arg r, prev arg y)
  end

module Curry =
  struct
    let one = (@@)
    let succ k f x = k (fun tup -> f (x, tup))
  end

module Uncurry =
  struct
    let one = (@@)
    let succ k f (x,y) = k (f x) y
  end

module LogicAdder :
  sig
    val zero : goal -> goal
    val succ : ('a -> State.t -> 'd) -> (('e, 'f) injected -> 'a) -> State.t -> ('e, 'f) injected * 'd
  end = struct
    let zero f      = f
    let succ prev f = call_fresh (fun logic st -> (logic, prev (f logic) st))
  end

module ApplyAsStream = struct
  (* There we have a tuple of logic variables and a stream
   * and we want to make a stream of tuples
   **)

  (* every numeral is a function from tuple -> state -> reified_tuple *)
  let one tup state = make_rr tup state

  let succ prev (h,tl) state = (make_rr h state, prev tl state)

  (* Usage: let reified_tuple_stream = wrap ((s s s 1) tuple) stream in ... *)
  let wrap = Stream.map
end

let succ n () =
  let adder, app, ext, uncurr = n () in
  (LogicAdder.succ adder, ApplyAsStream.succ app, ExtractDeepest.succ ext, Uncurry.succ uncurr)

let one   () = (LogicAdder.(succ zero)), ApplyAsStream.one, ExtractDeepest.ext2, Uncurry.one
let two   () = succ one   ()
let three () = succ two   ()
let four  () = succ three ()
let five  () = succ four  ()

let q     = one
let qr    = two
let qrs   = three
let qrst  = four
let qrstu = five

let run n goalish f =
  Log.clear ();
  LOG[perf] (Log.run#enter);

  let adder, appN, ext, uncurr = n () in
  let helper tup =
    let args, stream = ext tup in
    (* we normalize stream before reification *)
    let stream =
      Stream.bind stream (fun st -> Stream.of_list @@ State.normalize st args)
    in
    Stream.map (uncurr f) @@ ApplyAsStream.wrap (appN args) stream
  in
  let result = helper (adder goalish @@ State.empty ()) in

  LOG[perf] (
    Log.run#leave;
    printf "Run report:\n%s" @@ Log.report ()
  );
  result

(** ************************************************************************* *)
(** Tabling primitives                                                        *)

module Table :
  sig
    (* Type of `answer` term.
     * Answer term is a term where all free variables are renamed to 0 ... n.
     *)
    type answer

    (* Type of table.
     * Table is a map from answer term to the set of answer terms,
     * i.e. answer -> [answer]
     *)
    type t

    val create   : unit -> t
    val abstract : 'a -> State.t -> answer

    val master : t -> answer -> 'a -> goal -> goal
    val slave  : t -> answer -> 'a -> goal
  end = struct
    type answer = Env.t * Obj.t * Disequality.cnf

    module Cache :
      sig
        type t

        val create    : unit -> t

        val add       : t -> answer -> unit
        val contains  : t -> answer -> bool
        val consume   : t -> 'a -> goal
      end =
      struct
        type t = answer list ref

        let create () = ref []

        let add cache answ =
          cache := List.cons answ !cache

        let contains cache (_, answ, diseq) =
          ListLabels.exists !cache
            ~f:(fun (_, answ', diseq') ->
              (* all variables in both terms are renamed to 0 ... n (and constraints are sorted),
               * because of that simple equivalence test is enough.
               * TODO: maybe we need [is_more_general answ' answ] test here
               * TODO: maybe there is more clever way to compare disequalities
               *)
               (answ = answ') && (diseq = diseq')
            )

        let consume cache args =
          let open State in fun {env; subst; scope} as st ->
          let st = State.incr_scope st in
          let scope = State.scope st in
          (* [helper iter seen] consumes answer terms from cache one by one
           *   until [iter] (i.e. current pointer into cache list) is not equal to [seen]
           *   (i.e. to the head of seen part of the cache list)
           *)
          let rec helper iter seen =
            if iter == seen then
              (* update `seen` - pointer to already seen part of cache *)
              let seen = !cache in
              (* delayed check that current head of cache is not equal to head of seen part *)
              let is_ready () = seen != !cache  in
              (* delayed thunk starts to consume unseen part of cache  *)
              Stream.suspend ~is_ready @@ fun () -> helper !cache seen
            else
              (* consume one answer term from cache *)
              let answ_env, answ_term, answ_ctrs = List.hd iter in
              let tail = List.tl iter in
              (* `lift` answer term to current environment *)
              let mapping, answ_term = Subst.refresh ~scope env answ_env Subst.empty answ_term in
              match State.unify (Obj.repr args) answ_term st with
                | Some ({subst=subst'; ctrs=ctrs'} as st') ->
                  begin
                  (* `lift` answer constraints to current environment *)
                  let _, answ_ctrs = Disequality.refresh ~mapping ~scope env answ_env Subst.empty answ_ctrs in
                  let answ_ctrs = Disequality.of_cnf env answ_ctrs in
                  try
                    (* check answ_ctrs against external substitution *)
                    let ctrs = Disequality.check ~prefix:(Subst.split subst) env subst' answ_ctrs in
                    let f = Stream.from_fun @@ fun () -> helper tail seen in
                    Stream.cons {st' with ctrs = Disequality.merge env ctrs' ctrs} f
                  with Disequality_violated -> helper tail seen
                  end
                | None -> helper tail seen
          in
          helper !cache []

      end

    type t = (Obj.t, Cache.t) Hashtbl.t

    let create () = Hashtbl.create 1031

    let empty_diseq =
      Disequality.to_cnf (Env.create ~anchor:Var.tabling_env) Subst.empty Disequality.empty

    let abstract args =
      let open State in fun {env; subst} ->
      let tenv = Env.create ~anchor:Var.tabling_env in
      (tenv, Obj.repr @@ snd @@ Subst.refresh ~scope:Var.tabling_scope tenv env subst args, empty_diseq)

    let extract_ctrs mapping answ_env env subst ctrs args =
      let fv = Subst.free_vars env subst args in
      let cs = Disequality.project env subst (Disequality.to_cnf env subst ctrs) fv in
      Disequality.normalize @@ snd @@ Disequality.refresh ~mapping ~scope:Var.tabling_scope answ_env env subst cs

    let extract_answer args =
      let open State in fun {env; subst; ctrs} ->
      let answ_env = Env.create ~anchor:Var.tabling_env in
      let mapping, answ_term = Subst.refresh ~scope:Var.tabling_scope answ_env env subst args in
      let answ_ctrs = extract_ctrs mapping answ_env env subst ctrs args in
      (answ_env, Obj.repr answ_term, answ_ctrs)

    let master tbl (_, k, _) args g =
      (* create new cache entry in table *)
      let cache = Cache.create () in
      Hashtbl.add tbl k cache;
      let open State in fun ({env; subst; ctrs} as st) ->
      (* This `fake` goal checks whether cache already contains new answer.
       * If not then this new answer is added to the cache.
       *)
      let hook ({env=env'; subst=subst'; ctrs=ctrs'} as st') =
        let answ = extract_answer args st' in
        if not (Cache.contains cache answ) then begin
          Cache.add cache answ;
          try
            (* TODO: we only need to check diff, i.e. [subst' \ subst] *)
            let ctrs = Disequality.check ~prefix:(Subst.split subst') env subst' ctrs in
            success {st' with ctrs = Disequality.merge env ctrs ctrs'}
          with Disequality_violated -> failure ()
        end
        else failure ()
      in
      (g &&& hook) {st with ctrs = Disequality.empty}

    let slave tbl (_, k, _) args =
      let open State in fun ({env} as st) ->
      let cache = Hashtbl.find tbl k in
      Cache.consume cache args st
  end

module Tabling =
  struct
    let succ n () =
      let currier, uncurrier = n () in
      let sc = (Curry.succ : (('a -> 'b) -> 'c) -> ((((_, _) injected as 'k) * 'a -> 'b) -> 'k -> 'c)) in
      (sc currier, Uncurry.succ uncurrier)

    let one () = ((Curry.(one) : ((_, _) injected -> _) as 'x -> 'x), Uncurry.one)

    let two   () = succ one ()
    let three () = succ two ()
    let four  () = succ three ()
    let five  () = succ four ()

    let tabled' tbl g args st =
      let key = Table.abstract args st in
      try
        Table.slave tbl key args st
      with Not_found ->
        Table.master tbl key args (g args) st

    let tabled n g =
      let tbl = Table.create () in
      let currier, uncurrier = n () in
      currier (fun tup ->
        tabled' tbl (uncurrier g) tup
      )

    let tabledrec n g_norec =
      let tbl = Table.create () in
      let currier, uncurrier = n () in
      let g = ref (fun _ -> assert false) in
      let g_rec args = uncurrier (g_norec !g) args in
      let g_tabled = tabled' tbl g_rec in
      g := currier (fun tup ->
        g_tabled tup
      );
      !g
end

(* Tracing/debugging stuff *)

(* module State

    let show  (env, subst, constr, scp) =
      sprintf "st {%s, %s} scope=%d" (Subst.show subst) (Constraints.show ~env constr) scp
*)

(* module Subst
    let show m =
      let b = Buffer.create 40 in
      Buffer.add_string b "subst {\n";
      M.iter (fun i {new_val} -> bprintf b "  %d -> %s;\n" i (generic_show new_val)) m;
      Buffer.add_string b "}";
      Buffer.contents b
=======


let unify ?p (x: _ injected) y =
  Trace.(trace two @@ unif ?p) x y (
    let open State in fun {env; subst; ctrs; scope} as st ->
    match Subst.unify env x y scope subst with
    | None -> failure ~reason:"Unification failed" st
    | Some (prefix, s) ->
        try
          let ctrs' = Constraints.check ~prefix env s ctrs in
          success {st with subst=s; ctrs=ctrs'}
        with Disequality_violated ->
          failure ~reason:"Disequality constraints violated" st
  )

let (===) x y = unify x y

let diseq ?p x y =
  Trace.(trace two @@ diseq ?p) x y (
    let open State in fun {env; subst; ctrs; scope} as st ->
    (* For disequalities we unify in non-local scope to prevent defiling *)
    match Subst.unify env x y non_local_scope subst with
    | None -> success st
    | Some ([],_) -> failure ~reason:"Constraint cannot be fulfilled" st
    | Some (prefix,_) ->
        let ctrs' = Constraints.extend ~prefix env ctrs in
        success {st with ctrs=ctrs'}
  )

let (=/=) x y = diseq x y

let delay : (unit -> goal) -> goal = fun g ->
  fun st -> MKStream.from_fun (fun () -> g () st)
>>>>>>> 81053c4... WIP: tabling

    let pretty_show is_var m =
      let b = Buffer.create 40 in
      bprintf b "subst {\n";
      M.iter (fun i {new_val} -> bprintf b "  %d -> %s;\n" i (pretty_generic_show is_var new_val)) m;
      bprintf b "}";
      Buffer.contents b
*)

(* module Constraints

  let bprintf_single ~env b cs =
    let rec helper = function
    | [] -> ()
    | c :: tl ->
          bprintf b "%d -> %s;" (!!!c.Subst.var : Var.t).index (pretty_generic_show (Env.is_var env) c.Subst.term);
          helper tl
    in
    helper cs

  let show_single ~env (c: single) =
    let b = Buffer.create 40 in
    bprintf b " ( ";
    let () = bprintf_single ~env b c in
    bprintf b " ) ";
    Buffer.contents b

  let show ~env cstore =
    let b = Buffer.create 40 in
    M.iter (fun k css ->
      bprintf b "\t%d -> [ " k;
      List.iter (fun s -> bprintf_single ~env b s) css;
      bprintf b " ]\n";
    ) cstore;
    Buffer.contents b

*)


(*
let generic_show ?(maxdepth=99999) x =
  let x = Obj.repr x in
  let b = Buffer.create 1024 in
  let rec inner depth o =
    if depth > maxdepth then Buffer.add_string b "..." else
      match wrap o with
      | Invalid n                                         -> Buffer.add_string b (Printf.sprintf "<invalid %d>" n)
      | Unboxed s when Obj.(string_tag = (tag @@ repr s)) -> bprintf b "\"%s\"" (!!!s)
      | Unboxed n when !!!n = 0                           -> Buffer.add_string b "[]"
      | Unboxed n                                         -> Buffer.add_string b (Printf.sprintf "int<%d>" (!!!n))
      | Boxed  (t, l, f) ->
          Buffer.add_string b (Printf.sprintf "boxed %d <" t);
          for i = 0 to l - 1 do (inner (depth+1) (f i); if i<l-1 then Buffer.add_string b " ") done;
          Buffer.add_string b ">"
  in
  inner 0 x;
  Buffer.contents b

(* TODO *)
let pretty_generic_show ?(maxdepth= 99999) is_var x =
  let x = Obj.repr x in
  let b = Buffer.create 1024 in
  let rec inner depth term =
    if depth > maxdepth then Buffer.add_string b "..." else
    if is_var !!!term then begin
      let var = (!!!term : Var.t) in
      match var.subst with
      | Some term ->
          bprintf b "{ _.%d with subst=" var.index;
          inner (depth+1) term;
          bprintf b " }"
      | None -> bprintf b "_.%d" var.index
    end else match wrap term with
      | Invalid n                                         -> bprintf b "<invalid %d>" n
      | Unboxed s when Obj.(string_tag = (tag @@ repr s)) -> bprintf b "\"%s\"" (!!!s)
      | Unboxed n when !!!n = 0                           -> Buffer.add_string b "[]"
      | Unboxed n                                         -> bprintf b  "int<%d>" (!!!n)
      | Boxed  (t, l, f) ->
        Buffer.add_string b (Printf.sprintf "boxed %d <" t);
        for i = 0 to l - 1 do (inner (depth+1) (f i); if i<l-1 then Buffer.add_string b " ") done;
        Buffer.add_string b ">"
  in
  inner 0 x;
  Buffer.contents b

let trace msg g = fun state ->
  printf "%s: %s\n%!" msg (State.show state);
  g state

let reify_with_state (env,subs,cs,_) term = reify' env subs (Constraints.reify env subs cs) (Obj.repr term)

let project1 ~msg : (helper -> 'b -> string) -> ('a, 'b) injected -> goal = fun shower q st ->
  printf "%s %s\n%!" msg (shower (helper_of_state st) @@ Obj.magic @@ reify_with_state st q);
  success st

let project2 ~msg : (helper -> 'b -> string) -> (('a, 'b) injected as 'v) -> 'v -> goal = fun shower q r st ->
  printf "%s '%s' and '%s'\n%!" msg (shower (helper_of_state st) @@ Obj.magic @@ reify_with_state st q)
                                    (shower (helper_of_state st) @@ Obj.magic @@ reify_with_state st r);
  success st

let project3 ~msg : (helper -> 'b -> string) -> (('a, 'b) injected as 'v) -> 'v -> 'v -> goal = fun shower q r s st ->
  printf "%s '%s' and '%s' and '%s'\n%!" msg
    (shower (helper_of_state st) @@ Obj.magic @@ reify_with_state st q)
    (shower (helper_of_state st) @@ Obj.magic @@ reify_with_state st r)
    (shower (helper_of_state st) @@ Obj.magic @@ reify_with_state st s);
  success st

let unitrace ?loc shower x y = fun st ->
  incr logged_unif_counter;

  let ans = (x === y) st in
  (* printf "%d: unify '%s' and '%s'" !logged_unif_counter (shower (helper_of_state st) x) (shower (helper_of_state st) y);
  (match loc with Some l -> printf " on %s" l | None -> ());

  if Stream.is_nil ans then printfn "  -"
  else  printfn "  +"; *)
  ans

let diseqtrace shower x y = fun st ->
  incr logged_diseq_counter;
  let ans = (x =/= y) st in
  (* printf "%d: (=/=) '%s' and '%s'" !logged_diseq_counter
    (shower (helper_of_state st) x)
    (shower (helper_of_state st) y);
  if Stream.is_nil ans then printfn "  -"
  else  printfn "  +"; *)
  ans;;

(* ***************************** a la relational StdLib here ***************  *)

let report_counters () = ()
*)
