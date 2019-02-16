(*
 * MiniKanren: PPX extension that expands `fresh`.
 *
 * Copyright (C) 2015-2017
 * Dmitrii Kosarev
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
open Ppxlib
open Ppxlib.Ast_helper
open Ocaml_common.Ast_mapper
open StdLabels
module Location = Ppxlib.Import_for_core.Location

module Exp = struct
  include Ast_helper.Exp
  let const_string s = Exp.constant @@ Pconst_string (s, None)
end

let is_state_pattern pat =
  match pat.ppat_desc with
  | Ppat_var v when v.txt = "st" || v.txt = "state" -> Some v.txt
  | _ -> None

let classify_name ~f e =
  match e.pexp_desc with
  | Pexp_ident i when f i.txt -> true
  | _ -> false
let need_insert_fname ~name e =
  classify_name e ~f:((=) (Lident name))
  (* match e.pexp_desc with
  | Pexp_ident i when i.txt = Lident name -> true
  | _ -> false *)

let is_defer = need_insert_fname ~name:"defer"
let is_conde = need_insert_fname ~name:"conde"
let is_fresh = need_insert_fname ~name:"fresh"
let is_call_fresh = need_insert_fname ~name:"call_fresh"
let is_unif =
  classify_name
    ~f:(function
        | Lident s -> (String.length s >=3) && (String.sub s 0 3 = "===")
        | _ -> false
        )

let is_conj = need_insert_fname ~name:"conj"
let is_conj_list = need_insert_fname ~name:"?&"

let is_disj e =
  need_insert_fname ~name:"disj" e || need_insert_fname ~name:"|||" e

let option_map ~f = function Some x -> Some (f x) | None -> None
let option_bind ~f = function Some x -> f x | None -> None

exception Not_an_ident
let reconstruct_args e =
  let are_all_idents (xs: (_*expression) list) =
    try Some (List.map (fun (_,e) ->
                        match e.pexp_desc with
                        | Pexp_ident {txt=(Longident.Lident i);_} -> i
                        | _ -> raise Not_an_ident) xs)
    with Not_an_ident -> None
  in
  match e.pexp_desc with
  | Pexp_apply ({pexp_desc=Pexp_ident {txt=Longident.Lident arg1; _}}, ys) ->
     (* fresh (var1 var2 var3) body *)
      option_map (are_all_idents ys) ~f:(fun xs -> arg1::xs )

  | Pexp_ident {txt=Longident.Lident arg1; _} ->
     (* fresh arg0 body *)
     Some [arg1]
  | _ -> None

let list_fold ~f ~initer xs =
  match xs with
  | [] -> failwith "bad argument"
  | start::xs -> List.fold_left ~init:(initer start) ~f xs

let list_fold_right0 ~f ~initer xs =
  let rec helper = function
  | [] -> failwith "bad_argument"
  | x::xs -> list_fold ~initer ~f:(fun acc x -> f x acc) (x::xs)
  in
  helper (List.rev xs)

let my_list ~loc es =
  List.fold_right ~init:[%expr []] es ~f:(fun x acc -> [%expr [%e x] :: [%e acc]])

let parse_to_list alist =
  let rec helper acc = function
  | Pexp_construct (loc, None ) when loc.txt = Lident "[]" -> acc
  | Pexp_construct (loc, Some {pexp_desc=Pexp_tuple [y1;y2]; _})
      when loc.txt = Lident "::" ->
      helper (y1::acc) y2.pexp_desc
  | _ -> []
  in
  List.rev @@ helper [] alist

let rec pamk_e mapper e : expression =
  let loc = e.pexp_loc in
  match e.pexp_desc with
  | Pexp_apply (_,[]) -> e
  | Pexp_apply (e1,(_,alist)::args) when is_conj_list e1 ->
      let clauses : expression list = parse_to_list alist.pexp_desc in
      let ans = list_fold_right0 clauses
        ~initer:(fun x -> x)
        ~f:(fun x acc -> [%expr [%e x] &&& [%e acc]])
      in
      pamk_e mapper ans
  | Pexp_apply (e1,(_,alist)::otherargs) when is_conde e1 ->
      let clauses : expression list = parse_to_list alist.pexp_desc in
      [%expr
        conde [%e my_list ~loc @@ List.map (fun e -> pamk_e mapper e) clauses ]
      ]
  | Pexp_apply (e1,[args]) when is_fresh e1 ->
      (* bad syntax -- no body*)
     e
  | Pexp_apply (e1, (_,args) :: body) when is_fresh e1 -> begin
      assert (List.length body > 0);

      let body : expression =
        let body = List.map snd body in
        [%expr delay (fun () -> [%e
                       match body with
                       | [] -> assert false
                       | [body] ->
                         (* we omitte bind* here*)
                         pamk_e mapper body
                       | body ->
                         let xs = List.map (pamk_e mapper) body in
                         list_fold_right0 ~initer:(fun x -> x) xs ~f:(fun x acc ->
                             [%expr [%e x] &&& [%e acc] ]
                           )
                     ])]
      in
      match reconstruct_args args with
      | None ->
         eprintf "Can't reconstruct args of 'fresh'";
         {e with pexp_desc=Pexp_apply (e1,[Nolabel, body]) }
      | Some (vars: string list) ->
        let rec loop = function
          | a::b::c::tl ->
            let pa = Pat.var ~loc (Location.mkloc a loc) in
            let pb = Pat.var ~loc (Location.mkloc b loc) in
            let pc = Pat.var ~loc (Location.mkloc c loc) in
            [%expr MiniKanren.Fresh.three (fun [%p pa] [%p pb] [%p pc] -> [%e loop tl])]
          | a::b::[] ->
            let pa = Pat.var ~loc (Location.mkloc a loc) in
            let pb = Pat.var ~loc (Location.mkloc b loc) in
            [%expr MiniKanren.Fresh.two (fun [%p pa] [%p pb] -> [%e body])]
          | a::[] ->
            let pa = Pat.var ~loc (Location.mkloc a loc) in
            [%expr MiniKanren.Fresh.one (fun [%p pa] -> [%e body])]
          | [] -> body
        in
        loop vars
    end
  | Pexp_apply (d, [(_,body)]) when is_defer d ->
      let ans = [%expr MKStream.inc (fun () -> [%e pamk_e mapper body])] in
      ans
  | Pexp_apply (d, body) when is_unif d ->
      Exp.apply ~loc:e.pexp_loc d body
  | Pexp_apply (e, xs) ->
      let ans = Pexp_apply (mapper.expr mapper e,
                                   List.map ~f:(fun (lbl,e) -> (lbl, mapper.expr mapper e)) xs ) in
      {e with pexp_desc = ans}
  | Pexp_fun (l,opt,pat,e) ->
     { e with pexp_desc=Pexp_fun(l,opt,pat, mapper.expr mapper e) }

  | Pexp_construct (_, None) -> e
  | Pexp_construct (id, Some e1) -> { e with pexp_desc = Pexp_construct (id, Some (mapper.expr mapper e1)) }

  | Pexp_tuple es -> {e with pexp_desc=Pexp_tuple (List.map (mapper.expr mapper) es) }
  | Pexp_let   (_recflag, vbs,where_expr) ->
     let vbs_new = List.map (fun vb -> {vb with pvb_expr=mapper.expr mapper vb.pvb_expr}) vbs
     in
     {e with pexp_desc=Pexp_let(_recflag, vbs_new, mapper.expr mapper where_expr) }
  | Pexp_sequence (e1, e2) ->
     {e with pexp_desc=Pexp_sequence(mapper.expr mapper e1,mapper.expr mapper e2) }
  | Pexp_open (_flag, _loc, ee) ->
     { e with pexp_desc=Pexp_open (_flag, _loc, mapper.expr mapper ee) }
  | Pexp_newtype (name, ee) ->
     { e with pexp_desc=Pexp_newtype(name, mapper.expr mapper ee) }
  | Pexp_constraint (ee,t) ->
     { e with pexp_desc=Pexp_constraint(mapper.expr mapper ee, t) }
  (* TODO: support all cases *)
  | _ -> e

let pa_minikanren =
  { default_mapper with expr = fun mapper e -> pamk_e mapper e }

let () =
  Driver.register_transformation
    ~impl:(fun s -> pa_minikanren.structure pa_minikanren s)
    "pa_minikanren"
