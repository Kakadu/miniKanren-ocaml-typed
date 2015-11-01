(*
 * MiniKanren: miniKanren primitives implementation.
 * Copyright (C) 2015
 * Dmitri Boulytchev, Dmitry Kosarev, St.Petersburg State University
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

(** {1 Implementation of miniKanren primitives} *)

(** {2 Basic modules and types} *)

module type LOGGER = sig
  type t
  val log: string -> t list -> t
end
module UnitLogger: LOGGER

(** Lazy streams *)
module Stream :
  sig

    (** Type of the stream *)
    type 'a t

    (** Lazy constructor *)
    val from_fun : (unit -> 'a t) -> 'a t
  end

module Make : functor (Logger: LOGGER) -> sig
(** State (needed to perform calculations) *)
module State :
  sig
    (** State type *)
    type t

    (** Printing helper *)
    val show : t -> string
  end

module Logger: LOGGER

(** Goal converts a state into a lazy stream of states *)
type goal = State.t -> State.t Stream.t

(** {2 GT-based printing functions} *)

(** [show_var st x k] inspects [x] w.r.t. state [st] and either shows it
    as a variable (bound in [st]) or returns the value generated by
    continuation [k] *)
val show_var : State.t -> 'a -> (unit -> string) -> string

(** Type synonyms *)
type    int       = GT.int
type    string    = GT.string
type 'a list      = 'a GT.list
type    bool      = GT.bool
type    char      = GT.char
type    unit      = GT.unit
type    int32     = GT.int32
type    int64     = GT.int64
type    nativeint = GT.nativeint

(** OO printing transformers *)
class mkshow_string_t    : object method t_string    : State.t -> string    -> string end
class mkshow_int_t       : object method t_int       : State.t -> int       -> string end
class mkshow_bool_t      : object method t_bool      : State.t -> bool      -> string end
class mkshow_char_t      : object method t_char      : State.t -> char      -> string end
class mkshow_unit_t      : object method t_unit      : State.t -> unit      -> string end
class mkshow_int32_t     : object method t_int32     : State.t -> int32     -> string end
class mkshow_int64_t     : object method t_int64     : State.t -> int64     -> string end
class mkshow_nativeint_t : object method t_nativeint : State.t -> nativeint -> string end
class ['a] mkshow_list_t :
  object
    method c_Cons :
      State.t ->
      (State.t, 'a GT.list, string, < a : State.t -> 'a -> string >) GT.a ->
      (State.t, 'a, string, < a : State.t -> 'a -> string >) GT.a ->
      (State.t, 'a GT.list, string, < a : State.t -> 'a -> string >) GT.a ->
      string
    method c_Nil :
      State.t ->
      (State.t, 'a GT.list, string, < a : State.t -> 'a -> string >) GT.a ->
      string
    method t_list :
      (State.t -> 'a -> string) -> State.t -> 'a GT.list -> string
  end

(** Type-indexed containers *)
val int :
  (('a, 'b) #GT.int_tt -> 'a -> GT.int -> 'b,
   < compare : GT.int -> GT.int -> GT.comparison;
     eq : GT.int -> GT.int -> GT.bool; foldl : 'c -> GT.int -> 'c;
     foldr : 'd -> GT.int -> 'd; html : GT.int -> HTMLView.er;
     map : GT.int -> GT.int; mkshow : State.t -> GT.int -> string;
     show : GT.int -> string >)
  GT.t
val string :
  (('a, 'b) #GT.string_tt -> 'a -> GT.string -> 'b,
   < compare : GT.string -> GT.string -> GT.comparison;
     eq : GT.string -> GT.string -> GT.bool; foldl : 'c -> GT.string -> 'c;
     foldr : 'd -> GT.string -> 'd; html : GT.string -> HTMLView.er;
     map : GT.string -> GT.string; mkshow : State.t -> GT.string -> string;
     show : GT.string -> GT.string >)
  GT.t
val bool :
  (('a, 'b) #GT.string_tt -> 'a -> GT.string -> 'b,
   < compare : GT.bool -> GT.bool -> GT.comparison;
     eq : GT.bool -> GT.bool -> GT.bool; foldl : 'c -> GT.bool -> 'c;
     foldr : 'd -> GT.bool -> 'd; html : GT.bool -> HTMLView.er;
     map : GT.bool -> GT.bool; mkshow : State.t -> GT.bool -> string;
     show : GT.bool -> string >)
  GT.t
val char :
  (('a, 'b) #GT.char_tt -> 'a -> GT.char -> 'b,
   < compare : GT.char -> GT.char -> GT.comparison;
     eq : GT.char -> GT.char -> GT.bool; foldl : 'c -> GT.char -> 'c;
     foldr : 'd -> GT.char -> 'd; html : GT.char -> HTMLView.er;
     map : GT.char -> GT.char; mkshow : State.t -> GT.char -> string;
     show : GT.char -> GT.string >)
  GT.t
val unit :
  (('a, 'b) #GT.unit_tt -> 'a -> GT.unit -> 'b,
   < compare : GT.unit -> GT.unit -> GT.comparison;
     eq : GT.unit -> GT.unit -> GT.bool; foldl : 'c -> GT.unit -> 'c;
     foldr : 'd -> GT.unit -> 'd; html : GT.unit -> HTMLView.er;
     map : GT.unit -> GT.unit; mkshow : State.t -> GT.unit -> string;
     show : GT.unit -> GT.string >)
  GT.t
val int32 :
  (('a, 'b) #GT.int32_tt -> 'a -> GT.int32 -> 'b,
   < compare : GT.int32 -> GT.int32 -> GT.comparison;
     eq : GT.int32 -> GT.int32 -> GT.bool; foldl : 'c -> GT.int32 -> 'c;
     foldr : 'd -> GT.int32 -> 'd; html : GT.int32 -> HTMLView.er;
     map : GT.int32 -> GT.int32; mkshow : State.t -> GT.int32 -> string;
     show : GT.int32 -> GT.string >)
  GT.t
val int64 :
  (('a, 'b) #GT.int64_tt -> 'a -> GT.int64 -> 'b,
   < compare : GT.int64 -> GT.int64 -> GT.comparison;
     eq : GT.int64 -> GT.int64 -> GT.bool; foldl : 'c -> GT.int64 -> 'c;
     foldr : 'd -> GT.int64 -> 'd; html : GT.int64 -> HTMLView.er;
     map : GT.int64 -> GT.int64; mkshow : State.t -> GT.int64 -> string;
     show : GT.int64 -> GT.string >)
  GT.t
val nativeint :
  (('a, 'b) #GT.nativeint_tt -> 'a -> GT.nativeint -> 'b,
   < compare : GT.nativeint -> GT.nativeint -> GT.comparison;
     eq : GT.nativeint -> GT.nativeint -> GT.bool;
     foldl : 'c -> GT.nativeint -> 'c; foldr : 'd -> GT.nativeint -> 'd;
     html : GT.nativeint -> HTMLView.er; map : GT.nativeint -> GT.nativeint;
     mkshow : State.t -> GT.nativeint -> string;
     show : GT.nativeint -> GT.string >)
  GT.t
val list :
  (('a -> 'b -> 'c) ->
   ('b, 'a, 'c, 'd, 'e) #GT.list_tt -> 'd -> 'b GT.list -> 'e,
   < compare : ('f -> 'f -> GT.comparison) ->
               'f GT.list -> 'f GT.list -> GT.comparison;
     eq : ('g -> 'g -> GT.bool) -> 'g GT.list -> 'g GT.list -> GT.bool;
     foldl : ('h -> 'i -> 'h) -> 'h -> 'i GT.list -> 'h;
     foldr : ('j -> 'k -> 'j) -> 'j -> 'k GT.list -> 'j;
     html : ('l -> HTMLView.er) -> 'l GT.list -> HTMLView.er;
     map : ('m -> 'n) -> 'm GT.list -> 'n GT.list;
     mkshow : (State.t -> 'o -> string) -> State.t -> 'o GT.list -> string;
     show : ('p -> GT.string) -> 'p GT.list -> GT.string >)
  GT.t
val option :
  (('a -> 'b -> 'c) ->
   ('b, 'a, 'c, 'd, 'e) #GT.option_tt -> 'd -> 'b GT.option -> 'e,
   < compare : ('f -> 'f -> GT.comparison) ->
               'f GT.option -> 'f GT.option -> GT.comparison;
     eq : ('g -> 'g -> GT.bool) -> 'g GT.option -> 'g GT.option -> GT.bool;
     foldl : ('h -> 'i -> 'h) -> 'h -> 'i GT.option -> 'h;
     foldr : ('j -> 'k -> 'j) -> 'j -> 'k GT.option -> 'j;
     html : ('l -> HTMLView.er) -> 'l GT.option -> HTMLView.er;
     map : ('m -> 'n) -> 'm GT.option -> 'n GT.option;
     mkshow : (State.t -> 'o -> string) -> State.t -> 'o GT.option -> string;
     show : ('p -> GT.string) -> 'p GT.option -> GT.string >)
  GT.t

(** MiniKanren show type-indexed wrapper *)
val mkshow : ('a, < mkshow : 'b; .. >) GT.t -> 'b

(** {2 miniKanren basic primitives} *)

(** [call_fresh f] creates a fresh logical variable and passes it to the
    parameter *)
val call_fresh : ('a -> State.t -> 'b) -> State.t -> 'b

(** [x === y] creates a goal, which performs a unifications of
    [x] and [y] *)
val (===) : 'a -> 'a -> goal

(** [conj s1 s2] creates a goal, which is a conjunction of its arguments *)
val conj : goal -> goal -> goal

(** [&&&] is left-associative infix synonym for [conj] *)
val (&&&) : goal -> goal -> goal

(** [disj s1 s2] creates a goal, which is a disjunction of its arguments *)
val disj : goal -> goal -> goal

(** [|||] is left-associative infix synonym for [disj] *)
val (|||) : goal -> goal -> goal

(** [?| [s1; s2; ...; sk]] calculates [s1 ||| s2 ||| ... ||| sk] for a
    non-empty list of goals *)
val (?|) : goal list -> goal

(** [conde] is a synonym for [?|] *)
val conde : goal list -> goal

(** [?& [s1; s2; ...; sk]] calculates [s1 &&& s2 && ... &&& sk] for a
    non-empty list of goals *)
val (?&) : goal list -> goal

(** {2 Top-level running primitives} *)

(** [run s] runs a state transformer [s] (not necessarily a goal) in
    initial state *)
val run : (State.t -> 'a) -> 'a

(** [refine s x] refines a logical variable [x] (created with [fresh]) w.r.t.
    state [s] *)
val refine : State.t -> 'a -> 'a

(** [take ?(n=k) s] takes at most [k] first answers from the lazy
    stream [s] (reexported from MKStream for convenience) *)
val take : ?n:int -> State.t Stream.t -> State.t list

end
