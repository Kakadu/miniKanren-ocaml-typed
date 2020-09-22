open Logic

type inti = (int, int logic) injected

type t

val empty : unit -> t

(* Performed after unification *)
val recheck: Env.t -> Subst.t -> t -> Subst.Binding.t list -> t option

val check: t -> t option

(** Adding new constraints *)

val eq: inti -> inti -> t -> t option
val neq: inti -> inti -> t -> t option
val lt: inti -> inti -> t -> t option

val domain: inti -> int list -> t -> t option
