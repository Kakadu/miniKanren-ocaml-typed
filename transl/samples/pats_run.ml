open OCanren
open Tester

open Pats

let id x = x

let pp_rhs fmt = Format.fprintf fmt "%d"
let pp_maybe fa fmt = function
| None -> Format.fprintf fmt "None"
| Some x -> Format.fprintf fmt "(Some %a)" fa x

let leaf s = eConstr !!s @@ Std.List.nil ()
(* let nil = eConstr !!"nil" @@ Std.List.nil () *)
(* let z = eConstr !!"z" @@ Std.List.nil () *)
let pair a b = eConstr !!"pair" (Std.List.list [a;b])

let rec show_match_logic x =
  let rec helper = function
  | Scru          -> "Scru"
  | Field (n,r) ->
    Printf.sprintf "Field (_,%s)" (show_match_logic r)
  in
  GT.show OCanren.logic helper x

let show_match x =
  let rec helper = function
  | Scru        -> "Scru"
  | Field (n,r) -> Printf.sprintf "Field (_,%s)" (helper r)
  in
  helper x

let rec nat_reifier env n =
  For_gnat.reify nat_reifier env n

let rec match_reifier env x =
  For_gmatchable.reify nat_reifier match_reifier env x

let rec show_expr x =
  match x with
  | EConstr (s, xs) ->
    Printf.sprintf "(%s %s)"
      (GT.show GT.string s)
      (GT.show Std.List.ground show_expr xs)


let rec show_expr_logic x =
  let rec helper x =
    match x with
    | EConstr (s, xs) ->
      Printf.sprintf "(%s %s)"
        (GT.show OCanren.logic (GT.show GT.string) s)
        (GT.show Std.List.logic show_expr_logic xs)
  in
  GT.show OCanren.logic helper x



let rec expr_reifier env x =
  For_gexpr.reify OCanren.reify (Std.List.reify expr_reifier) env x

let checkAnswer q c r = eval_ir ((===) q) ((===) c) r

let _ =
  run_exn (Format.asprintf "%a" (pp_maybe pp_rhs)) 1 q qh ("answers", fun q ->
    checkAnswer (pair (leaf "aaa") (leaf "bbb"))
      (iFTag !!"aab" (field (z()) (scru ())) (int !!1) (int !!2))
      q
  )

let _ =
  runR expr_reifier show_expr show_expr_logic
        1 q qh ("answers", fun q ->
     checkAnswer
        q
        (iFTag !!"aab" (field (z()) (scru ())) (int !!1) (int !!2))
        (Std.some (!!2))
  )

module Pattern = struct
  type ground = (string, ground Std.List.ground) gpattern
  type logic = (string OCanren.logic, logic Std.List.logic) gpattern OCanren.logic
  type injected = (ground, logic) OCanren.injected

  let rec height = function
  | WildCard  -> 0
  | PConstr (_,ps) ->
    GT.foldl Std.List.ground (fun acc x -> max acc (height x)) 0 ps + 1

  let ground_list_length xs =
    GT.foldl Std.List.ground (fun acc _ -> acc+1) 0 xs

  module ArityMap = Map.Make(Base.String)
  exception Bad

  let get_arities (pat: ground) =
    let rec helper acc = function
      | WildCard -> acc
      | PConstr (name, xs) ->
          let acc =
            let arity = ground_list_length xs in
            try
              match ArityMap.find name acc with
              | ar when ar = arity -> acc
              | _ -> raise Bad
            with  Not_found -> ArityMap.add name arity acc
          in
          GT.foldl OCanren.Std.List.ground (fun acc p -> helper acc p) acc xs
    in
    try Some (helper ArityMap.empty pat)
    with Bad -> None
end




let make_expr_generator (pats: Pattern.ground list) =
  let height = List.fold_left
    (fun acc p -> max acc (Pattern.height p)) 0 pats in
  let arity_map =
    let default_name = ":HACK" in
    match Pattern.get_arities (PConstr (default_name, Std.List.of_list id pats)) with
    | Some ar -> Pattern.ArityMap.remove default_name ar
    | None    -> failwith "bad arities"
  in

  let generator_0 _ = fresh (q) (q === q)  in
  let rec loop prev_size (prev_size_gen : Expr.injected -> goal) =
    if prev_size > height then prev_size_gen
    else
      let next_gen =
        ArityMap.to_seq arity_map |>
        Seq.map (fun (name,c) q ->
          add_freshes c (fun vars ->
            List.fold_left (fun acc v -> acc &&& prev_size_gen v)
              (q === Expr.constr (inj@@lift name) (Std.List.list vars))
              vars
            )
        )  |> List.of_seq |> (fun xs q -> conde @@ List.map (fun g -> g q) xs)
      in
      loop (prev_size+1) next_gen
  in
  (* generator_0 *)
  loop 0 generator_0
