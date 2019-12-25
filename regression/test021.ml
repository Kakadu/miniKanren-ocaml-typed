include struct
   open OCanren
   type ('name, 'terms) term = Term of 'name * 'terms

   let fmt_term fname fterms fmt (Term (s, xs)) =
     Format.fprintf fmt "('%a %a)" fname s fterms xs

   type ground = (string,               ground OCanren.Std.List.ground) term
   type logic  = (string OCanren.logic, logic  OCanren.Std.List.logic)  term OCanren.logic
   type tinj = (ground, logic) injected

   module F = OCanren.Fmap2(struct
      type  ('a, 'b) t = ('a,'b) term
      let fmap fa fb (Term (a,b)) = Term (fa a, fb b)
   end)

   let w name xs = inj @@ F.distrib @@ Term (name, xs)
   (* in [w name xs] xs is obliged to be a list of terms. Is it what is expected? *)

   let leaf name = w name (Std.List.nil ())

   let rec term_reify env t : logic =
      F.reify OCanren.reify (OCanren.Std.List.reify term_reify) env t
   let pp_string fmt = Format.fprintf fmt "%s"
   let rec pp_term_logic fmt t =
      let rec helper fmt = function
      | Term (name, Value Std.List.Nil) -> GT.fmt logic pp_string fmt name
      | Term (name, xs) ->
          Format.fprintf fmt "(%a %a)" (GT.fmt logic pp_string) name
          (GT.fmt Std.List.logic pp_term_logic) xs
      in
      GT.fmt OCanren.logic helper fmt t

end

let () =
  Format.pp_set_margin Format.std_formatter 140;
  Format.pp_set_max_indent Format.std_formatter 2000

let pp_reify_term fmt rr = Format.fprintf fmt "%a" pp_term_logic (rr#reify term_reify)

let hack msg var =
  let open OCanren.Std in
  trace1 msg var pp_reify_term

let hackboth msg v1 v2 =
  let open OCanren.Std in
  trace2 msg v1 v2 pp_reify_term pp_reify_term

let my_term_check2 msg a b =
  let open OCanren.Std in
  let pp fmt x = match Obj.magic x with
  | x ->
    (* Format.fprintf fmt "{here} " *)
    Format.fprintf fmt "%a" pp_reify_term x
  in
  term_check2 pp msg (Obj.repr a) (Obj.repr b)

let my_term_check1 msg a =
  let open OCanren.Std in
  let pp fmt x = match Obj.magic x with
  | x ->
    (* Format.fprintf fmt "{here} " *)
    Format.fprintf fmt "%a" pp_reify_term x
  in
  term_check1 pp msg (Obj.repr a) 

(* ****** Relational stuff ******************** *)
let (!!) x = OCanren.(inj @@ lift x)

include struct
  open OCanren
  open OCanren.Std
let ia33554436 a = w !!"ia33554436" (Std.List.list[a])
let valuetype33554777 = w !!"valuetype33554777" (Std.List.list[])
let object33554493 = w !!"object33554493" (Std.List.list[])
let rec contravariant_subtype a b =
  conde
    [ (b === a) &&& (is_valuetype b)
    ; (is_reference b) &&& (subtype b a)
    ]
and covariant_subtype a b =
  conde
    [ (a === b) &&& (is_valuetype a)
    ; (is_reference a) &&& (subtype a b)
    ]
and default_constructor a = (a === object33554493)
and is_reference a =
  conde
    [ fresh (b)
       (a === ia33554436 b)
    ; (a === valuetype33554777)
    ; (a === object33554493)
    ]
and is_unmanaged a = failure
and is_valuetype a = failure
and not_contravariant_subtype a b =
  conde
    [ (b =/= a) &&& (is_valuetype b)
    ; (is_reference b) &&& (not_subtype b a)
    ]
and not_covariant_subtype a b =
  conde
    [ (a =/= b) &&& (is_valuetype a)
    ; (is_reference a) &&& (not_subtype a b)
    ]
and not_subtype a b =
  conde
    [ fresh (c d)
       (a === ia33554436 c)
       (b === ia33554436 d)
       (not_covariant_subtype c d)
    ; fresh (c)
       (a === ia33554436 c)
       (b === valuetype33554777)
    ; fresh (c)
       (a === valuetype33554777)
       (b === ia33554436 c)
    ; fresh (c)
       (a === object33554493)
       (b === ia33554436 c)
    ; (a === object33554493) &&& (b === valuetype33554777)
    ]
and subtype a b =
(*  (hackboth "\nsubtype a b" a b) &&&
  (term_check2 "check: subtype {a,b}" a b) &&&*)
  conde
    [ fresh (c d)
       (a === ia33554436 c)
       (b === ia33554436 d)
       (covariant_subtype c d)
    ; fresh (c)
       (a === ia33554436 c)
       (b === object33554493)
    ; (a === valuetype33554777) &&& (b === valuetype33554777)
    ; (a === valuetype33554777) &&& (b === object33554493)
    ; (a === object33554493) &&& (b === object33554493)
    ]

let rec simple_test a  =
  (hack "\nsimple_test a" a) &&&
  (my_term_check1 "check: simple_test {a}" a) &&&
  conde
    [ fresh (c d)
       (c === ia33554436 a)       
       (simple_test c)
    ]
    
let rec simple_test2 a b =
  (hackboth "\nsimple_test2 a b" a b) &&&
  (my_term_check2 "check: simple_test2 {a;b}" a b) &&&
  conde
    [ fresh (c d)
       (c === ia33554436 a)       
       (d === ia33554436 b)
       (simple_test2 c d)
    ]
end



let () =
   let my_reify r = r#reify term_reify in
   let stream =
      let open OCanren  in
      let open OCanren.Std in
      run (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ one))))))))))
      (fun a b c d e f g h i j k ->
(*        (simple_test2 a (ia33554436 a))*)
(*        (simple_test a)*)
        (simple_test (ia33554436 a))
        (* (subtype a (ia33554436 a)) *)
        (* &&& (subtype b (ia33554436 a)) &&& (subtype valuetype33554777 c) &&& (subtype d (ia33554436 d)) &&& (subtype e (ia33554436 d)) &&& (subtype f a) &&& (subtype g a) &&& (subtype f h) &&& (subtype g h) &&& (subtype c h) &&& (subtype i h) &&& (subtype j h) &&& (subtype k h) &&& (subtype a (ia33554436 d)) &&& (subtype d (ia33554436 a)) &&& (subtype a (ia33554436 d)) &&& (subtype d (ia33554436 a)) &&& (default_constructor c) &&& (is_reference j) *)
      )
      (fun a b c d e f g h i j k -> (my_reify a,my_reify b,my_reify c,my_reify d,my_reify e,my_reify f,my_reify g,my_reify h,my_reify i,my_reify j,my_reify k))
   in
 
    let answers = OCanren.Stream.take ~n:1 stream in 
 
    match answers with
    | [] -> print_endline "no answers"
    | [((a,b,c,d,e,f,g,h,i,j,k))] ->
       Format.printf "(%a,%a,%a,%a,%a,%a,%a,%a,%a,%a,%a)\n%!" pp_term_logic a pp_term_logic b pp_term_logic c pp_term_logic d pp_term_logic e pp_term_logic f pp_term_logic g pp_term_logic h pp_term_logic i pp_term_logic j pp_term_logic k
    | _ -> failwith "should not happen"
   
