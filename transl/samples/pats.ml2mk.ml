let list_map_all f xs =
  let rec helper y = match y with
  | [] -> true
  | x::xs -> match f x with
  | Some _ -> helper xs
  | None -> false
  in
  helper xs

let rec list_all f z = match z with
| [] -> true
| x::xs ->  if f x
            then list_all f xs
            else false

(* let rec list_length xs = match xs with
| [] -> 0
| x::xs -> 1 + list_length xs *)

let rec same_length xs ys = match (xs, ys) with
| _::xs,_::ys -> same_length xs ys
| [],_::_ -> false
| _::_,[] -> false
| [],[] -> true

let rec list_combine xs ys =
  match xs,ys with
  | [],[] -> []
  | x::xs,y::ys -> (x, y) :: (list_combine xs ys)

type nat = Z | S of nat

let rec list_nth_nat idx xs = match (idx, xs) with
| (Z, x::_) -> x
| (S n, _::xs) -> list_nth_nat n xs


type pattern = WildCard | PConstr of string * pattern list
type expr = EConstr of string * expr list

let rec eval_pat s pats =
  let rec eval1pat s p =
    match s,p with
    | (_,WildCard) -> true
    | (EConstr (tag1, es), PConstr (tag2, ps)) ->
        if (tag1 = tag2) && (same_length ps es)
        then
          let pairs = list_combine ps es in
          list_all (fun x -> match x with (p,e) -> eval1pat e p) pairs
        else false
  in
  match pats with
  | [] -> None
  | (p,rhs)::ps ->
      if eval1pat s p
      then Some rhs
      else eval_pat s ps


(* *************************** IR thing ********************************* *)

type matchable = Scru | Field of nat * matchable
type ir = Fail | IFTag of string * matchable * ir * ir | Int of int


let rec eval_ir s ir =
  let rec  eval_m s m = match m with
    | Scru -> s
    | Field (n, m) ->
      match eval_m s m with
      | EConstr (_, es) -> list_nth_nat n es
  in
  match ir with
  | Fail -> None
  | Int n -> Some n
  | IFTag (tag, scru, th, el) ->
      match eval_m s scru with
      | EConstr (tag2, args) ->
        if tag2 = tag
        then eval_ir s th
        else eval_ir s el
