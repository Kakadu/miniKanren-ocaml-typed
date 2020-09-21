open Logic
open Term
open Format

module T = Aez.Smt.Term
module F = Aez.Smt.Formula
module Solver = Aez.Smt.Make (struct end)
module Symbol = Aez.Smt.Symbol
module Type = Aez.Smt.Type

let (!!!) = Obj.magic;;

@type var_idx = GT.int with fmt
@type term = Var of var_idx | Const of GT.int with fmt
@type phormula =
  | FMDom of var_idx * GT.int GT.list
  | FMLT of term * term
  | FMLE of term * term
  | FMEQ of term * term
  | FMNEQ of term * term
  with fmt

type inti = (int, int logic) injected
type ph_desc = phormula list
type item = VarSet.t * ph_desc
type t = item list

let pp_ph_desc fmt =
  let pp_term fmt = function
    | Var n -> Format.fprintf fmt "_.%d" n
    | Const n -> Format.fprintf fmt "%d" n
  in
  let pp fmt = function
    | FMNEQ (l, r) -> Format.fprintf fmt "%a≠%a" pp_term l pp_term r
    | FMEQ  (l, r) -> Format.fprintf fmt "%a=%a" pp_term l pp_term r
    | FMLE  (l, r) -> Format.fprintf fmt "%a⩽%a" pp_term l pp_term r
    | FMLT  (l, r) -> Format.fprintf fmt "%a<%a" pp_term l pp_term r
    | FMDom (n,xs) -> Format.fprintf fmt "_.%d ∈ %a" n (GT.fmt GT.list @@ GT.fmt GT.int) xs
  in
  GT.fmt GT.list pp fmt


let var_of_idx idx = Aez.Hstring.make (sprintf "x%d" idx)
let decl_var idx =
  let x = var_of_idx idx in
  try
    Symbol.declare x [] Type.type_int
  with
    | Aez.Smt.Error (Aez.Smt.DuplicateSymb _) -> ()
    | Aez.Smt.Error (Aez.Smt.DuplicateTypeName _) -> ()

let wrap_term = function
  | Var n   ->
      decl_var n;
      T.make_app (var_of_idx n) []
  | Const m -> T.make_int (Num.num_of_int m)

let check_item_list is =
  (* Construct request to solver there and check that it is satisfiable.
  *)

  try
(*    Format.printf "checking_item_list: %a\n%!" pp_ph_desc is;*)
    Solver.clear ();
    let wrap_binop op a b = F.make_lit op [ wrap_term a; wrap_term b ] in
    let make op xs =
      match op,xs with
      | F.Or, [x] -> x
      | _ -> F.make op xs
    in
    is |> Stdlib.List.iteri (fun id -> function
      | FMLT (a,b) ->
(*          Format.printf "%s %d\n%!" __FILE__ __LINE__;*)
          Solver.assume ~id @@ wrap_binop F.Lt a b
      | FMLE (a,b) ->
(*          Format.printf "%s %d\n%!" __FILE__ __LINE__;*)
          Solver.assume ~id @@ wrap_binop F.Le a b
      | FMEQ (a,b) ->
(*          Format.printf "%s %d\n%!" __FILE__ __LINE__;*)
          Solver.assume ~id @@ wrap_binop F.Eq a b
      | FMNEQ(a,b) ->
(*          Format.printf "%s %d\n%!" __FILE__ __LINE__;*)
          Solver.assume ~id @@ wrap_binop F.Neq a b
      | (FMDom(v,xs)) ->
(*          Format.printf "%s %d %a\n%!" __FILE__ __LINE__ (GT.fmt item) xxx;*)
          Solver.assume ~id @@
          make F.Or (xs |> Stdlib.List.map (fun n ->
            wrap_binop F.Eq (Var v) (Const n)
          ))
    );

    if is <> [] then Solver.check ();
    true
  with
    | Aez.Smt.Unsat _core ->
        Format.printf "UNSAT\n%!";
        false
    | Aez.Smt.Error e ->
        let open Aez in
        match e with
        | Smt.UnknownSymb s ->
            failwith (Printf.sprintf "unknown symb %s on %s %d\n%!" (Hstring.view s) __FILE__ __LINE__)
        | DuplicateSymb s ->
            failwith (Printf.sprintf "DuplicateSymb %s\n%!" (Aez.Hstring.view s))
        | DuplicateTypeName s -> failwith (Printf.sprintf "DuplicateTypeName %s\n%!" (Hstring.view s))
        | UnknownType s -> failwith (Printf.sprintf "unknown type '%s'. \n%!" (Hstring.view s))
(*
type lookup_rez =
  | Two of (VarSet.t * ph_desc) * (VarSet.t * ph_desc)
  | One of (VarSet.t * ph_desc)
  | Zero

let rec fold_cps ~f ~init xs =
  match xs with
  | [] -> init
  | x::xs -> f init x (fun acc -> fold_cps ~f ~init:acc xs)
*)
(*
let lookup a b (set,is) =

  let extend v = function
  | Zero -> One v
  | One v1 -> Two (v1, v)
  | Two (_,_) -> failwith "should not happpen"
  in
  let flt v1 v2 xs =
    fold_cps ~init:Zero ~f:(fun acc x k ->
      match x with
      | (set, items) when Term.VarSet.mem v1 set ->
    )
  in
    List.fold_left (fun acc x ->
      match (acc,x) with
      | T
    ) Zero xs
  in

  let f x =
    match Term.is_var x with
    | None ->
  | Some v1, Some v2 -> begin
      let verdict =

      in
  end
*)


let add_binop op (a: inti) (b:inti) (set,is) : item =
  let set, ta, tb =
    let f set x = match Term.var x with
      | None   -> (set, Const (Obj.magic x))
      | Some v -> (VarSet.add v set, Var v.Term.Var.index)
    in
    let set,ta = f set !!!a in
    let set,tb = f set !!!b in
    (set, ta, tb)
  in
  let is = (op ta tb) :: is in
  (set, is)

let check store =
  (* Format.printf "Check called\n%!"; *)
  if check_item_list @@ snd store
  then Some store
  else None


let rec fold_cps ~f ~init xs =
  match xs with
  | [] -> init
  | x::xs -> f init x xs (fun acc -> fold_cps ~f ~init:acc xs)

let empty () = []

exception Bad
type lookup_rez =
  | Zero
  | One of (VarSet.t * ph_desc)
  | Two of (VarSet.t * ph_desc) * (VarSet.t * ph_desc)

exception Extended of t

let recheck_helper1 ~do_add op (store: t) a b =
(*  Format.printf "recheck_helper1 %s %d\n%!" __FILE__ __LINE__;*)

  let on_var_and_term v term (store: t) : t option =
(*    Format.printf "on_var_and_term: term=%d %s %d\n%!" !!!term __FILE__ __LINE__;*)
    let ans =
      fold_cps ~init:(Zero,[]) store ~f:(fun acc ((set,is) as a) tl k ->
        if VarSet.mem v set
        then
          match acc with
          | Zero,visited -> k (One a, visited @ tl)
          | One (_,_),_ -> failwith "Should not happen"
          | Two (_,_),_ -> failwith "Should not happen"
          (* let st = add_binop op !!!v !!!term (set, is) in
          match check st with
          | None -> raise Bad
          | Some item -> raise (Extended (acc @ item :: tl)) *)
        else
          let v,xs = acc in
          k (v,a::xs)
      )
    in
    let ext_and_check (set,phs,tl) =
    (* we need to prepend to tail new pack of constraints *)
      let set = VarSet.add v set in
      let h = add_binop op !!!v !!!term (set,phs) in
      match check h with
        | Some h -> Some (h::tl)
        | None -> None
    in
    match ans with
    | Zero,tl when do_add -> ext_and_check (VarSet.empty, [], tl)
    | Zero,_ -> Some store
    | One (s,is),tl -> ext_and_check (s,is,tl)
    | Two ((s1,ph1), (s2,ph2)),tl -> failwith "Should not happen"
  in

  let on_two_vars v1 v2 store =
    (* Format.printf "%s %d\n%!" __FILE__ __LINE__; *)
    let ext_set set = VarSet.(add v1 (add v2 set)) in
    let ans =
      fold_cps ~init:(Zero,[]) store ~f:(fun acc ((set,is) as a) tl k ->
        if VarSet.mem v1 set || VarSet.mem v2 set
        then begin
            match acc with
            | Zero,tl -> k (One a, tl)
            | One (s2,is2),tl2 ->
                let s3 = VarSet.(add v1 (add v2 (union s2 set))) in
                let is3 = Stdlib.List.append is is2 in
                (One (s3,is3), Stdlib.List.append tl2 tl)
            | Two (_,_),_ -> failwith "should not happen"
        end else
          let v,xs = acc in
          k (v,a::xs)
      )
    in

    let ext_and_check (set,phs,tl) =
    (* we need to prepend to tail new pack of constraints *)
      let set = ext_set set in
      let h = add_binop op !!!v1 !!!v2 (set,phs) in
      match check h with
        | Some h -> Some (h::tl)
        | None -> None
    in
    (* let (set,is,tl) =
      match ans with
      | Zero, tl -> (VarSet.empty, [], tl)
      | One (s,is),tl -> (s,is,tl)
    in *)
    match ans with
    | Zero,tl when do_add -> ext_and_check (VarSet.empty, [], tl)
    | Zero,_ -> Some store
    | One (s,is),tl -> ext_and_check (s,is,tl)
    | Two ((s1,ph1), (s2,ph2)),tl -> ext_and_check (VarSet.merge s1 s2, ph1@ph2, tl)
  in

(*  Format.printf "HACK: a= '%s', b = '%s'. %s %d\n%!" (Term.show !!!a) (Term.show !!!b) __FILE__ __LINE__;*)

  match Term.(var a, var b) with
  | None,None when !!!a = !!!b ->
(*      Format.printf "%s %d\n%!"  __FILE__ __LINE__;*)
      Some store
  | None,None                  ->
(*      Format.printf "%s %d\n%!"  __FILE__ __LINE__;*)
      None
  | Some v1, Some v2 ->
(*      Format.printf "%s %d\n%!"  __FILE__ __LINE__;*)
      on_two_vars v1 v2 store
  | Some v, None ->
(*      Format.printf "%s %d\n%!"  __FILE__ __LINE__;*)
      on_var_and_term v !!!b store
  | None, Some v ->
(*      Format.printf "%s %d\n%!"  __FILE__ __LINE__;*)
      on_var_and_term v !!!a store

let recheck_helper ~do_add op (store: t) (_prefix : Subst.Binding.t list) =
(*  if store <> [] then Format.printf "store is not empty\n%!";*)
  try
    Some (fold_cps ~init:store _prefix ~f:(fun acc bin _tl k ->
      let open Subst in
      match recheck_helper1 ~do_add op acc !!!(bin.Binding.var) !!!(bin.Binding.term) with
      | None -> raise Bad
      | Some ans -> k ans
    ))
  with Bad -> None

let recheck _env _subst (store: t) (_prefix : Subst.Binding.t list) =
  recheck_helper (fun a b -> FMEQ (a,b)) ~do_add:false store _prefix

let check store : t option =
  try
    store |> Stdlib.List.iter (fun (_set,is) ->
      if not (check_item_list is) then raise Bad
    );
    Some store
  with Bad -> None



let neq x y store =
  recheck_helper1 (fun a b -> FMNEQ (a,b)) ~do_add:true store x y

let eq  x y store : t option =
  recheck_helper1 (fun a b -> FMEQ (a,b)) ~do_add:true store x y

let lt  x y store =
  recheck_helper1 (fun a b -> FMLT (a,b)) ~do_add:true store x y

let (=/=) = neq

let domain (v: inti) ints store =
  let v =
    match Term.var !!!v with
    | None -> failwith "should not happen"
    | Some v  -> v
  in
(*  *)
  try
    let _ =
      fold_cps ~init:[] store ~f:(fun acc (set,is) tl k ->
        if VarSet.mem v set
        then begin
          let d = FMDom (v.Term.Var.index, ints) in
          let is = d::is in
          if check_item_list is
          then raise (Extended ((VarSet.add v set, is) :: (acc @ tl)))
          else raise Bad
        end else
          k ((set,is)::acc)
      )
    in
    let new_ = (VarSet.add !!!v VarSet.empty, [FMDom (v.Term.Var.index, ints)]) in
    Some (new_ :: store)
  with
    | Bad -> None
    | Extended t -> Some t
