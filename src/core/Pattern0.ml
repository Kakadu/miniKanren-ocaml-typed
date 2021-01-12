let failwithf fmt = Printf.ksprintf failwith fmt

(*
  Influenced by
  https://github.com/ocaml-ppx/ppxlib/blob/master/src/ast_pattern.mli
*)

include (
  struct
    type location = Env.t

    exception Expected of string

    let fail loc expected = raise (Expected  expected)

    type context =
      { (* [matched] counts how many constructors have been matched. This is used to find what
           pattern matches the most some piece of ast in [Ast_pattern.alt]. In the case where
           all branches fail to match, we report the error from the one that matches the
           most.
           This is only incremented by combinators that can fail. *)
        mutable matched: int }

    type ('matched_value, 'k, 'k_result) t =
      | T of (context -> location -> 'matched_value -> 'k -> 'k_result)

    let save_context ctx = ctx.matched
    let restore_context ctx backup = ctx.matched <- backup
    let incr_matched c = c.matched <- c.matched + 1

    let parse (T f) loc ?on_error x k =
      try f {matched= 0} loc x k
      with Expected expected -> (
        match on_error with
        | None -> failwithf "%s expected" expected
        | Some f -> f () )

    let __ = T (fun ctx _loc x k -> incr_matched ctx; k x)
    let __any = T (fun ctx _loc _ k -> k)

    (* various convenience functions *)

    let alt (T f1) (T f2) =
      T
        (fun ctx loc x k ->
          let backup = save_context ctx in
          try f1 ctx loc x k
          with e1 -> (
            let m1 = save_context ctx in
            restore_context ctx backup;
            try f2 ctx loc x k
            with e2 ->
              let m2 = save_context ctx in
              if m1 >= m2 then (restore_context ctx m1; raise e1) else raise e2 )
          )

    let ( ||| ) = alt

    let many (T f) =
      T
        (fun ctx loc l k ->
          k (ListLabels.map l ~f:(fun x -> f ctx loc x (fun x -> x))) )

    let map (T func) ~f = T (fun ctx loc x k -> func ctx loc x (f k))
    let ( >>| ) t f = map t ~f

    let map_result (T func) ~f = T (fun ctx loc x k -> f (func ctx loc x k))
    let map0 (T func) ~f = T (fun ctx loc x k -> func ctx loc x (           k  f     ))
    let map1 (T func) ~f = T (fun ctx loc x k -> func ctx loc x (fun a   -> k (f a  )))
  end :
    sig
      type location = Env.t
      type context

      exception Expected of string

      val fail : location -> string -> 'a

      type ('matched_value, 'k, 'k_result) t =
        | T of (context -> location -> 'matched_value -> 'k -> 'k_result)

      val parse :
        ('a, 'b, 'c) t -> location -> ?on_error:(unit -> 'c) -> 'a -> 'b -> 'c

      val incr_matched : context -> unit
      val save_context : context -> int
      val restore_context : context -> int -> unit
      val __ : ('a, 'a -> 'b, 'b) t
      val __any : ('a, 'b, 'b) t
      val alt : ('a, 'b, 'c) t -> ('a, 'b, 'c) t -> ('a, 'b, 'c) t

      val ( ||| ) : ('a, 'b, 'c) t -> ('a, 'b, 'c) t -> ('a, 'b, 'c) t
      (** Same as [alt] *)

      val map : ('a, 'b, 'c) t -> f:('d -> 'b) -> ('a, 'd, 'c) t

      val ( >>| ) : ('a, 'b, 'c) t -> ('d -> 'b) -> ('a, 'd, 'c) t
      (** Same as [map] *)

      val map_result : ('a, 'b, 'c) t -> f:('c -> 'd) -> ('a, 'b, 'd) t

      val map0 : ('a, 'b, 'c) t -> f:'v  -> ('a, 'v -> 'b, 'c) t
      val map1 : ('a, 'v1 ->        'b, 'c) t -> f:('v1 ->        'v) -> ('a, 'v -> 'b, 'c) t
    end )
