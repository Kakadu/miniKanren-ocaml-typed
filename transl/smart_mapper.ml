open Printf
open Typedtree
open Asttypes
open Ast_helper

module Untypeast = struct
  include Untypeast

  let pattern {pat_desc; pat_loc=loc} =
    match pat_desc with
    | Tpat_any -> Pat.any ~loc ()
    | Tpat_var (_,str) -> Pat.var ~loc str
    | _ -> failwith "Not implemented"

  let type_declaration = default_mapper.type_declaration default_mapper
  let expr = default_mapper.expr default_mapper
end
module Exp = struct
  include Exp
  let of_longident ?(loc=Location.none) lident =
    { Parsetree.pexp_attributes = []
    ; pexp_loc = loc
    ; pexp_desc = Pexp_ident (Location.mkloc lident loc)
    }

  let of_string ?(loc=Location.none) s =
    Exp.ident ~loc (Location.mkloc (Longident.Lident s) loc)
end
module Pat = struct
  include Pat
  let of_string ?(loc=Location.none) s = Pat.var ~loc (Location.mkloc s loc)
end

class virtual ['self] smart_mapper = object (self: 'self)
  method virtual type_declaration: 'inh_tdecl -> type_declaration -> Parsetree.type_declaration
  method virtual expression: 'inh_expr -> expression -> Parsetree.expression
(*  method virtual match_: -> 'inh_expr -> Parsetree.expression*)
end



class virtual ['self] transformation = object(self: 'self)
  inherit ['self ] smart_mapper

  method type_declaration _ = Untypeast.type_declaration

  method expression inh e = match e.exp_desc with
    | Texp_constant _           -> self#translate_constant e
    | Texp_construct (n, _cd, es) -> self#translate_construct n.txt n.loc es
    | Texp_match (what, cs, _, _)  -> self#translate_match what cs e.exp_type
    | Texp_apply (func, args)   -> self#translate_apply func args e.exp_type
    | Texp_function {cases=[case1]; arg_label} when arg_label <> Nolabel ->
        Exp.fun_ arg_label None (Untypeast.pattern case1.c_lhs)
          (self#expression inh case1.c_rhs)
    | Texp_function {cases} ->
        let untype_case {c_lhs; c_guard; c_rhs} =
          { Parsetree.pc_lhs = Untypeast.pattern c_lhs
          ; pc_rhs = self#expression inh c_rhs
          ; pc_guard = None (* TODO: finish implementation *)
          }
        in
        Exp.function_ (List.map untype_case cases)
    (* | Texp_function _ -> assert false *)
    | Texp_ident (_, { txt = Longident.Lident name }, _) when name = "===" -> self#translate_eq e
    | _ -> Untypeast.expr e

  method structure {str_items; str_type; str_final_env} =
    List.concat @@ List.map (self#structure_item str_type str_final_env) str_items
  method structure_item _typ _env item =
    match item.str_desc with
    | Tstr_type (_,tdecls) -> Untypeast.untype_structure {str_items=[item]; str_type=_typ; str_final_env = _env }
    | Tstr_value (flg, vbs) -> self#value_bindings flg vbs
    | _ -> failwith "wtf"

  method virtual value_bindings : rec_flag -> Typedtree.value_binding list -> Parsetree.structure_item list
  method virtual translate_constant : expression -> Parsetree.expression
  method virtual translate_construct: Longident.t -> Location.t -> expression list -> Parsetree.expression
  method virtual translate_match : expression -> _ -> _ -> Parsetree.expression
  method virtual translate_eq : expression -> Parsetree.expression
  method virtual translate_apply :
        Typedtree.expression ->
        (Asttypes.arg_label * Typedtree.expression option) list ->
        Types.type_expr ->
        Parsetree.expression
end

let nolabelize xs = List.map (fun e -> (Nolabel,e)) xs
let map_deepest_lident ~f lident =
  let open Longident in
  let rec helper = function
    | Lident s -> Lident (f s)
    | Ldot (l, s) -> Ldot (l, f s)
    | Lapply (l, r) -> Lapply (l, helper r)
  in
  helper lident

class ['self] transformation_impl = object(self: 'self)
  inherit ['self] transformation

  val fresh_var_counter = ref 0
  val fresh_var_prefix = "q"
  method create_fresh_var_name =
    let name = sprintf "%s%d" fresh_var_prefix !fresh_var_counter in
    incr fresh_var_counter;
    name

  method value_bindings flg xs =
    (*List.map (fun {vb_expr;vb_loc} -> [%stri let x = 1]) xs*)
    List.map (fun {vb_expr;vb_loc; vb_pat} ->
      Str.value flg [Vb.mk (Untypeast.pattern vb_pat) @@ self#expression () vb_expr]
    ) xs
  method translate_constant _ = assert false
  method translate_construct lident loc args =
    Exp.of_longident ~loc (map_deepest_lident Util.mangle_construct_name lident)


  (* Handle ((match `expr` with `cases`) : `typ`) *)
  method translate_match expr cases typ =
    let loc = expr.exp_loc in
    let argument_names =
      let rec calculate (typ : Types.type_expr) =
        match typ.Types.desc with
        | Types.Tarrow (_, _, right_typ, _) ->
              let name = self#create_fresh_var_name in
              name :: calculate right_typ
        | Types.Tlink typ             -> calculate typ
        | _                           -> [self#create_fresh_var_name]
      in
      calculate typ
    in
    let arguments =
      argument_names |>
      List.map (fun s -> Exp.ident ~loc (Location.mkloc (Longident.Lident s) loc))
    in

    let translated_expr = self#expression () expr in
    let unify_var_name  = self#create_fresh_var_name in
    (* let unify_var       = create_ident unify_var_name in *)
    let unify_expr      =
      [%expr [%e translated_expr] [%e Exp.of_string ~loc unify_var_name ]]
    in

    let translate_case {c_lhs = pattern; c_rhs = body} =
      (* | *)
      let real_arg_pats =
        match pattern.pat_desc with
        | Tpat_constant _             -> []
        | Tpat_construct (_, _, pats) -> pats
        | _ -> failwith "anything other constants and constructores in the matching patterns"
      in
      let get_var_name var = match var.pat_desc with
        | Tpat_var (ident, _) -> ident.name
        | _ -> assert false
      in

      let translated_body   = self#expression () body in
      (* We are applying translated_body to variables to get a goal *)
      let body_with_args    = Exp.apply translated_body (nolabelize arguments) in

      let real_arg_names = List.map get_var_name real_arg_pats in
      let real_args      = List.map (Exp.of_string ~loc) real_arg_names in

      let fresh_arg_names   = List.map (fun _ -> self#create_fresh_var_name) real_arg_pats in
      let fresh_args        = List.map (Exp.of_string ~loc) fresh_arg_names in

      let body_with_lambda  =
        List.fold_right
          (fun name acc -> Exp.fun_ Nolabel None (Pat.of_string ~loc name) acc)
          real_arg_names
          body_with_args
      in
      let lambda_arg_names   = List.map (fun _ -> self#create_fresh_var_name) real_args in
      let lambda_args        = List.map (Exp.of_string ~loc) fresh_arg_names in

      let unifies_for_subst = List.map2 (fun l r -> [%expr [%e l] === [%e r]])
          lambda_args fresh_args
      in

    
      1
    in

    assert false

  method translate_eq _ = assert false
  method translate_apply _ _ _ = assert false
end

let process tast =
  (new transformation_impl)#structure tast

