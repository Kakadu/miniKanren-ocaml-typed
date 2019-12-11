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

(* let rec nat_reifier env n =
  For_gnat.reify nat_reifier env n

let rec match_reifier env x =
  For_gmatchable.reify nat_reifier match_reifier env x *)


module Pattern = struct
  type ground = (string, ground Std.List.ground) gpattern
  type logic = (string OCanren.logic, logic Std.List.logic) gpattern OCanren.logic
  type injected = (ground, logic) OCanren.injected

  let constr = pConstr
  let wc = wildCard

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

module Expr = struct
  type ground = (string, ground Std.List.ground) gexpr
  type logic  = (string OCanren.logic, logic Std.List.logic) gexpr OCanren.logic
  type injected = (ground, logic) OCanren.injected

  let constr = eConstr
  let econstr s xs = EConstr (s, Std.List.of_list id xs)

  let rec show x =
    match x with
    | EConstr (s, xs) ->
      Printf.sprintf "(%s %s)"
        (GT.show GT.string s)
        (GT.show Std.List.ground show xs)

  let rec show_logic x =
    let rec helper x =
      match x with
      | EConstr (s, xs) ->
        Printf.sprintf "(%s %s)"
          (GT.show OCanren.logic (GT.show GT.string) s)
          (GT.show Std.List.logic show_logic xs)
    in
    GT.show OCanren.logic helper x

  let rec reify env x =
    For_gexpr.reify OCanren.reify (Std.List.reify reify) env x

end

let generate_demo_exprs pats =
  let height = List.fold_left
    (fun acc p -> max acc (Pattern.height p)) 0 pats in
  Printf.printf "height = %d\n%!" height;

  let arity_map =
    let default_name = ":HACK" in
    match Pattern.get_arities (PConstr (default_name, Std.List.of_list id pats)) with
    | Some ar -> Pattern.ArityMap.remove default_name ar
    | None    -> failwith "bad arities"
  in

  let dummy = Expr.econstr "DUMMY" [] in
  let height1 =
    Pattern.ArityMap.fold (fun k arity acc ->
      (Expr.econstr k @@ List.init arity (fun _ -> dummy)) :: acc
    ) arity_map []
  in
  List.iter (fun p -> Printf.printf "%s, " (Expr.show p)) height1;

  let rec populate_lists length orig =
    let rec helper n =
      if n<1 then failwith "bad argument"
      else if n=1 then orig
      else
        let prevs = helper (n-1) in
        List.concat_map (fun tl -> List.map (fun h -> h::tl) orig) prevs 
    in
    helper length
  in
  let rec builder acc curh =
    if curh > height
    then acc
    else
  ()

let checkAnswer q c r = eval_ir ((===) q) ((===) c) r

let _ =
  run_exn (Format.asprintf "%a" (pp_maybe pp_rhs)) 1 q qh ("answers", fun q ->
    checkAnswer (pair (leaf "aaa") (leaf "bbb"))
      (iFTag !!"aab" (field (z()) (scru ())) (int !!1) (int !!2))
      q
  )

let _ =
  runR Expr.reify Expr.show Expr.show_logic
        1 q qh ("answers", fun q ->
     checkAnswer
        q
        (iFTag !!"aab" (field (z()) (scru ())) (int !!1) (int !!2))
        (Std.some (!!2))
  )

let add_freshes n pregoal =
  let rec helper acc n =
    if n = 0 then pregoal acc
    else OCanren.Fresh.one (fun q -> helper (q::acc) (n-1))
  in
  helper [] n

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
        Pattern.ArityMap.to_seq arity_map |>
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
  loop 0 generator_0

let pwc = WildCard
let pconstr name xs = PConstr (name, Std.List.of_list id xs)
let pleaf s = pconstr s []
let pnil    = pleaf "nil"
let pcons a b = pconstr "cons" [a;b]
let ppair a b : Pattern.ground = pconstr "pair" [a;b]

let patterns1 : Pattern.ground list =
  [ ppair pnil pwc
  ; ppair pwc  pnil
  ; ppair (pcons pwc pwc) (pcons pwc pwc)
  ]


let _ =
  runR Expr.reify Expr.show Expr.show_logic 10
    q qh ("answers", make_expr_generator patterns1)

module Nat = struct
  type ground = ground gnat
  type logic = logic gnat OCanren.logic

  let z = z
  let s = s

  let rec reify env x = For_gnat.reify reify env x
end
module Matchable = struct
  type ground = (Nat.ground, ground) gmatchable
  type logic = (Nat.logic, logic) gmatchable OCanren.logic

  let scru = scru
  let field = field
  let rec reify env x =
    For_gmatchable.reify Nat.reify reify env x

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

end

module IR = struct
  type ground = (string, Matchable.ground, ground, ground) gir
  type logic = (string OCanren.logic, Matchable.logic, logic, logic) gir OCanren.logic

  let fail = fail
  let iftag = iFTag
  let int = int

  let rec reify env x =
    For_gir.reify OCanren.reify Matchable.reify reify reify env x

  let show e =
    let rec helper = function
    | _ -> Printf.sprintf "<ground ir>"
    in
    helper e

  let rec show_logic e =
    let rec helper = function
    | _ -> Printf.sprintf "<logic ir>"
    in
    GT.show OCanren.logic helper e
end

(* let _ =
  let pats = patterns1 in
  let all_exprs =
   let generator = make_expr_generator @@ List.map id patterns1 in
   let es_logic = run one generator (fun r -> r#reify Expr.reify)
     |> OCanren.Stream.take ~n:(2)
     |> List.map Expr.inject
   in
   (* let es_logic =
     if List.length es_logic > 2
     then List.take es_logic 2
     else es_logic
   in *)
   es_logic
 in

  (* final stuff *)
  runR IR.reify IR.show IR.show_logic 10
    q qh ("answers", make_expr_generator patterns1)

  () *)

let () =
  let () = generate_demo_exprs patterns1 in
  ()
