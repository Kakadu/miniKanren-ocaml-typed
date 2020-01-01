(*
 * OCanren.
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

let (!!!) = Obj.magic

type w = Unboxed of Obj.t | Boxed of int * int * (int -> Obj.t) | Invalid of int

let rec wrap (x : Obj.t) =
  Obj.(
    let is_valid_tag =
      List.fold_left
      (fun f t tag -> tag <> t && f tag)
      (fun _ -> true)
      [lazy_tag   ; closure_tag  ; object_tag  ; infix_tag ;
       forward_tag; no_scan_tag  ; abstract_tag; custom_tag;
       final_tag  ; unaligned_tag; out_of_heap_tag
      ]
    in
    let is_unboxed obj =
      is_int obj ||
      (fun t -> t = string_tag || t = double_tag) (tag obj)
    in
    if is_unboxed x
    then Unboxed x
    else
      let t = tag x in
      if is_valid_tag t
      then
        let f = if t = double_array_tag then !!! double_field else field in
        Boxed (t, size x, f x)
      else Invalid t
    )

let generic_show x =
  let x = Obj.repr x in
  let b = Buffer.create 1024 in
  let rec inner o =
    match wrap o with
    | Invalid n             -> Buffer.add_string b (Printf.sprintf "<invalid %d>" n)
    | Unboxed n when !!!n=0 -> Buffer.add_string b "[]"
    | Unboxed n             -> Buffer.add_string b (Printf.sprintf "int<%d>" (!!!n))
    | Boxed (t,l,f) when t=0 && l=1 && (match wrap (f 0) with Unboxed i when !!!i >=10 -> true | _ -> false) ->
       Printf.bprintf b "var%d" (match wrap (f 0) with Unboxed i -> !!!i | _ -> failwith "shit")

    | Boxed   (t, l, f) ->
        Buffer.add_string b (Printf.sprintf "boxed %d <" t);
        for i = 0 to l - 1 do (inner (f i); if i<l-1 then Buffer.add_string b " ") done;
        Buffer.add_string b ">"
  in
  inner x;
  Buffer.contents b

module Binding =
  struct
    type t =
      { var   : Term.Var.t
      ; term  : Term.t
      }

    let is_relevant env vs {var; term} =
      (Term.VarSet.mem var vs) ||
      (match VarEnv.var env term with Some v -> Term.VarSet.mem v vs | None -> false)

    let equal {var=v; term=t} {var=u; term=p} =
      (Term.Var.equal v u) || (Term.equal t p)

    let compare {var=v; term=t} {var=u; term=p} =
      let res = Term.Var.compare v u in
      if res <> 0 then res else Term.compare t p

    let hash {var; term} = Hashtbl.hash (Term.Var.hash var, Term.hash term)
  end

type t = Term.t Term.VarMap.t

let empty = Term.VarMap.empty

let of_list =
  ListLabels.fold_left ~init:empty ~f:(let open Binding in fun subst {var; term} ->
    if not @@ Term.VarMap.mem var subst then
      Term.VarMap.add var term subst
    else
      invalid_arg "OCanren fatal (Subst.of_list): invalid substituion"
  )

let of_map m = m

let split s = Term.VarMap.fold (fun var term xs -> Binding.({var; term})::xs) s []

type lterm = Var of Term.Var.t | Value of Term.t

let rec walk env subst x =
  (* walk var *)
  let rec walkv env subst v =
    VarEnv.check_exn env v;
    match v.Term.Var.subst with
    | Some term -> walkt env subst (Obj.magic term)
    | None ->
        try walkt env subst (Term.VarMap.find v subst)
        with Not_found -> Var v
  (* walk term *)
  and walkt env subst t =
    match VarEnv.var env t with
    | Some v -> walkv env subst v
    | None   -> Value t
  in
  walkv env subst x

(* same as [Term.map] but performs [walk] on the road *)
let map ~fvar ~fval env subst x =
  let rec deepfvar v =
    VarEnv.check_exn env v;
    match walk env subst v with
    | Var v   -> fvar v
    | Value x -> Term.map x ~fval ~fvar:deepfvar
  in
  Term.map x ~fval ~fvar:deepfvar

(* same as [Term.iter] but performs [walk] on the road *)
let iter ~fvar ~fval env subst x =
  let rec deepfvar v =
    VarEnv.check_exn env v;
    match walk env subst v with
    | Var v   -> fvar v
    | Value x -> Term.iter x ~fval ~fvar:deepfvar
  in
  Term.iter x ~fval ~fvar:deepfvar

(* same as [Term.fold] but performs [walk] on the road *)
let fold ~fvar ~fval ~init env subst x =
  let rec deepfvar acc v =
    VarEnv.check_exn env v;
    match walk env subst v with
    | Var v   -> fvar acc v
    | Value x -> Term.fold x ~fval ~fvar:deepfvar ~init:acc
  in
  Term.fold x ~init ~fval ~fvar:deepfvar

exception Occurs_check

let rec occurs env subst var term =
  iter env subst term
    ~fvar:(fun v -> if Term.Var.equal v var then raise Occurs_check)
    ~fval:(fun x -> ())

let extend ~scope ?(occ=true) env subst var term  =
  (* if occurs env subst var term then raise Occurs_check *)
  let () =
    if occ 
    then occurs env subst var term
    else Printf.printf "\toccurs check disabled\n"
  in
    (* assert (VarEnv.var env var <> VarEnv.var env term); *)

  (* It is safe to modify variables destructively if the case of scopes match.
   * There are two cases:
   * 1) If we do unification just after a conde, then the scope is already incremented and nothing goes into
   *    the fresh variables.
   * 2) If we do unification after a fresh, then in case of failure it doesn't matter if
   *    the variable is be distructively substituted: we will not look on it in future.
   *)
  if (scope = var.scope) && (scope <> Term.Var.non_local_scope)
  then begin
    var.subst <- Some (Obj.repr term);
    subst
  end
    else
      Term.VarMap.add var (Term.repr term) subst

exception Unification_failed

let unify ?(occurs=true) ?(subsume=false) ?(scope=Term.Var.non_local_scope) env subst x y =
  (* The idea is to do the unification and collect the unification prefix during the process *)
  let extend var term (prefix, subst) =
    let subst = extend ~scope ~occ:occurs env subst var term in
    (Binding.({var; term})::prefix, subst)
  in
  let rec helper x y acc =
    let open Term in
    fold2 x y ~init:acc
      ~fvar:(fun ((_, subst) as acc) x y ->
        match walk env subst x, walk env subst y with
        | Var x, Var y      ->
          if Var.equal x y then acc else extend x (Term.repr y) acc
        | Var x, Value y    -> extend x y acc
        | Value x, Var y    -> extend y x acc
        | Value x, Value y  -> helper x y acc
      )
      ~fval:(fun acc x y ->
          if x = y then acc else raise Unification_failed
      )
      ~fk:(fun ((_, subst) as acc) l v y ->
          if subsume && (l = Term.R)
          then 
            raise Unification_failed
          else match walk env subst v with
          | Var v    -> extend v y acc
          | Value x  -> helper x y acc
      )
  in
  try
    let x, y = Term.(repr x, repr y) in
    (*let () = Format.printf "\tGoing to unify:\n%!" in
    let () = Format.printf "\tx   = %s\n%!" (generic_show x) in 
    let () = Format.printf "\ty   = %s\n%!" (generic_show y) in *)
    Some (helper x y ([], subst))
  with Term.Different_shape _ ->
(*       Format.printf "\tunification failed: Different_shape\n%!"; *)
       None
     | Unification_failed ->  
(*       Format.printf "\tunification failed: Unification_failed\n%!"; *)
       None
     | Occurs_check -> 
(*       Format.printf "\tunification failed: Occurs_check\n%!"; *)
       None

let apply env subst x = Obj.magic @@
  map env subst (Term.repr x)
    ~fvar:(fun v -> Term.repr v)
    ~fval:(fun x -> Term.repr x)

let freevars env subst x =
  VarEnv.freevars env @@ apply env subst x

let is_bound = Term.VarMap.mem

let merge env subst1 subst2 = Term.VarMap.fold (fun var term -> function
  | Some s  -> begin
    match unify env s (Obj.magic var) term with
    | Some (_, s') -> Some s'
    | None         -> None
    end
  | None    -> None
) subst1 (Some subst2)

let merge_disjoint env =
  Term.VarMap.union (fun _ _ ->
    invalid_arg "OCanren fatal (Subst.merge_disjoint): substitutions intersect"
  )

let subsumed env subst =
  Term.VarMap.for_all (fun var term ->
    match unify env subst (Obj.magic var) term with
    | Some ([], _)  -> true
    | _             -> false
  )

module Answer =
  struct
    type t = Term.t

    let subsumed env x y =
      match unify ~subsume:true env empty y x with
      | Some _ -> true
      | None   -> false
  end

let reify env subst x =
  map env subst (Term.repr x)
    ~fvar:(fun v -> Term.repr v)
    ~fval:(fun x -> Term.repr x)

