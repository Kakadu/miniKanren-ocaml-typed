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

let (!!!) = Obj.repr

let () =
  Format.pp_set_margin Format.std_formatter 140;
  Format.pp_set_max_indent Format.std_formatter 2000

let pp_reify_term fmt rr = Format.fprintf fmt "%a" pp_term_logic (rr#reify term_reify)
let hack msg var  =
  let open OCanren.Std in
  trace1 msg var pp_reify_term

let hackboth msg v1 v2 =
  let open OCanren.Std in
  trace2 msg v1 v2 pp_reify_term pp_reify_term

let (!!) x = OCanren.(inj @@ lift x)

include struct
  open OCanren
  open OCanren.Std

  let (===?) = OCanren.(===?) pp_reify_term

let ia33554436 a = w !!"ia33554436" (Std.List.list[a])
let object33554493 = w !!"object33554493" (Std.List.list[])
let rec contravariant_subtype a b =
  (* relation "contravariant_subtype" [!!! a; !!! b] @@ *)
  conde
    [ (is_valuetype b) &&& (b === a)
    ; (is_reference b) &&& (subtype b a)
    ]
and covariant_subtype a b =
  (* relation "covariant_subtype" [!!! a; !!! b] @@ *)
  hackboth "covariant_subtype" a b &&&
  conde
    [ (is_valuetype a) &&& (a === b)
    ; (is_reference a) &&& (subtype a b)
    ]
and default_constructor a = (a === object33554493)
and is_unmanaged a = failure
and is_valuetype a = failure
and not_contravariant_subtype a b =
  (* relation "contravariant_subtype" [!!! a; !!! b] @@ *)
  conde
    [ (is_valuetype b) &&& (b =/= a)
    ; (is_reference b) &&& (not_subtype b a)
    ]
and not_covariant_subtype a b =
  (* relation "covariant_subtype" [!!! a; !!! b] @@ *)
  conde
    [ (is_valuetype a) &&& (a =/= b)
    ; (is_reference a) &&& (not_subtype a b)
    ]
and not_subtype a b =
  (* relation "subtype" [!!! a; !!! b] @@ *)
  hackboth "not_subtype" a b &&&
  conde
    [ fresh (c d)
       (a === ia33554436 c)
       (b === ia33554436 d)
       (not_covariant_subtype c d)
    ; fresh (c)
       (a === object33554493)
       (b === ia33554436 c)
    ]
and is_reference a =
  (hack "is_reference" a) &&&
  conde
    [ fresh (b)
       (a ===? (ia33554436 b))
    ; (a ===? object33554493)
    ]
and subtype a b =
  (hackboth "subtype" a b) &&&
  relation "subtype" [!!! a; !!! b] @@
  conde
    [
      fresh (c d)
       (a ===? ia33554436 c)
       (b ===? ia33554436 d)
       (* (covariant_subtype c d) *)
       (is_reference c)
       (subtype c d)
    ; fresh (c)
       (a ===? ia33554436 c)
       (b ===? object33554493)
    (* ; (a === object33554493) &&& (b === object33554493) *)
    ]
end

let () =
   let my_reify r = r#reify term_reify in
   let stream =
      let open OCanren  in
      let open OCanren.Std in
      run (succ one)
      (fun a b -> (subtype a (ia33554436 b))
                  &&& (subtype a (ia33554436 object33554493))
      )
      (fun a b -> (my_reify a,my_reify b))
   in
      let answers = OCanren.Stream.take ~n:1 stream in
      match answers with
      | [] -> print_endline "no answers"
      | [((a,b))] ->
         Format.printf "(%a,%a)\n%!" pp_term_logic a pp_term_logic b
      | _ -> failwith "should not happen"
