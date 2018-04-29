open Printf

(** We hide the context by instanciating a functor: *)
module Z3 = ZZ3.Make (struct let ctx = Z3.mk_context [] end)



(** The result of the functor is safe for opening (contains only types and modules. *)
open Z3


let () =
  Printf.printf "\nSimple test!\n%!" ;

  (** We create a solver for future usage. *)
  let solver = Solver.make () in

  (** We create new SMT variables and specify their types. *)
  let x = Symbol.declare Real "x" in
  let y = Symbol.declare Real "y" in

  (** We can define SMT formulas using an OCaml-like syntax.
      [!] transforms a symbol into a term.
  *)
  let t = T.( !y <= int 3 && !x + !y <= rat Q.(5 // 2)) in

  (** We assert the formula in the SMT solver. *)
  Solver.add ~solver t ;

  (** We can now solve it and extract the result: *)
  let result = Solver.check ~solver [] in

  let model = match result with
    | Unsat _ | Unkown _ -> failwith "Oh noees"
    | Sat (lazy model) -> model
  in

(** Finally we easily get back the values in the model as inferred by Z3 without any casting! *)
  let vy = Model.get_value ~model y in
  let vx = Model.get_value ~model x in

  Printf.printf "y = %s \nx = %s\n" (Q.to_string vy) (Q.to_string vx)

let () =
  printf "Presburger test 1\n";
  let solver = Solver.make () in
  let x = Symbol.declare Int "x" in
  Solver.add ~solver @@
  T.( int 4 < !x && !x < int 6);

  let model = match Solver.check ~solver [] with
    | Unsat _ | Unkown _ -> failwith "Oh noees"
    | Sat (lazy model) -> model
  in
  let vx = Model.get_value ~model x in
  Printf.printf "x = %s\n" (Z.to_string vx)
