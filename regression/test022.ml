open GT
open OCanren
open Tester

@type 'self gtree = Leaf | Node of 'self * 'self with show,gmap
@type  tree = tree gtree with show
@type ltree = ltree gtree logic with show

module T  = OCanren.Fmap(struct
  type 'a t = 'a gtree
  let fmap eta = GT.gmap gtree eta
end)


let rec tree_reify env t = T.reify tree_reify env t
let leaf = inj @@ T.distrib Leaf
let node (a,b) = inj @@ T.distrib (Node (a,b))

let (!!!) = Obj.magic;;
let (!) (x: int) = inj @@ lift x

(* Relations on lists *)

let rec appendo_dir a b ab =
  let open Std in
  conde [
    (a === Std.List.nil ()) &&& (b === ab);
    fresh (h t ab') (?& [
      (a === h % t);
      (appendo_dir t b ab');
      (h % ab' === ab);
    ])
  ]

let rec appendo_dir_wrapped a b ab = relation "appendo_dir" [!!! a; !!! b; !!! ab] @@
  let open Std in
  conde [
    (a === Std.List.nil ()) &&& (b === ab);
    fresh (h t ab') (?& [
      (a === h % t);
      (appendo_dir_wrapped t b ab');
      (h % ab' === ab);
    ])
  ]

let rec appendo_rev a b ab =
  let open Std in
  conde [
    (a === Std.List.nil ()) &&& (b === ab);
    fresh (h t ab') (?& [
      (a === h % t);
      (h % ab' === ab);
      (appendo_rev t b ab');
    ])
  ]

let rec appendo_rev_wrapped a b ab = relation "appendo_rev" [!!! a; !!! b; !!! ab] @@
  let open Std in
  conde [
    (a === Std.List.nil ()) &&& (b === ab);
    fresh (h t ab') (?& [
      (a === h % t);
      (h % ab' === ab);
      (appendo_rev_wrapped t b ab');
    ])
  ]

let rec reverso_dir a b =
  let open Std in
  conde [
    (a === Std.List.nil ()) &&& (b === a);
    fresh (h t a') (?& [
      (a === h % t);
      (reverso_dir t a');
      (appendo_dir a' !<h b);
    ])
  ]

let rec reverso_dir_wrapped a b = relation "reverso_dir" [!!! a; !!! b] @@
  let open Std in
  conde [
    (a === Std.List.nil ()) &&& (b === a);
    fresh (h t a') (?& [
      (a === h % t);
      (reverso_dir_wrapped t a');
      (appendo_dir_wrapped a' !<h b);
    ])
  ]

let rec reverso_rev a b =
  let open Std in
  conde [
    (a === Std.List.nil ()) &&& (b === a);
    fresh (h t a') (?& [
      (a === h % t);
      (appendo_rev a' !<h b);
      (reverso_rev t a');
    ])
  ]

let rec reverso_rev_wrapped a b = relation "reverso_rev" [!!! a; !!! b] @@
  let open Std in
  conde [
    (a === Std.List.nil ()) &&& (b === a);
    fresh (h t a') (?& [
      (a === h % t);
      (appendo_rev_wrapped a' !<h b);
      (reverso_rev_wrapped t a');
    ])
  ]


(* Sorting *)

let rec leo_wrapped a b = relation "leo" [!!! a; !!! b] @@
  let open Std in
  conde [
    (a === Nat.zero);
    fresh (a' b') ( ?&[
      (a === (Nat.succ a'));
      (b === (Nat.succ b'));
      (leo_wrapped a' b')
    ])
  ]

let rec lto_wrapped a b = relation "lto" [!!! a; !!! b] @@
  let open Std in
  conde [
    fresh (b') (?& [
      (a === Nat.zero);
      (b === (Nat.succ b'))
    ]);
    fresh (a' b') (?& [
      (a === (Nat.succ a'));
      (b === (Nat.succ b'));
      (leo_wrapped a' b')
    ])
  ]


let minmaxo a b min max =
  let open Std.Nat in
  conde
    [ (min === a) &&& (max === b) &&& (a <= b)
    ; (max === a) &&& (min === b) &&& (a >  b)
    ]


let minmaxo_wrapped a b min max = relation "minmaxo" [!!! a; !!! b; !!! min; !!! max] @@ Nat.(
    conde
      [ (min === a) &&& (max === b) &&& (leo_wrapped a b)
      ; (max === a) &&& (min === b) &&& (lto_wrapped b a)
      ]
  )

let rec smallesto_dir l s l' =
  let open Std in
  conde [
    (l === !< s) &&& (l' === Std.List.nil ());
    fresh (h t s' t' max) ( ?&[
      (l === h % t);
      (smallesto_dir t s' t');
      (minmaxo h s' s max);
      (l' === max % t');
    ])
  ]

let rec smallesto_dir_wrapped l s l' = relation "smallesto_dir" [!!! l; !!! s; !!! l'] @@
  let open Std in
  conde [
    (l === !< s) &&& (l' === Std.List.nil ());
    fresh (h t s' t' max) ( ?&[
      (l === h % t);
      (smallesto_dir_wrapped t s' t');
      (minmaxo_wrapped h s' s max);
      (l' === max % t');
    ])
  ]

let rec smallesto_rev l s l' =
  let open Std in
  conde [
    (l === !< s) &&& (l' === Std.List.nil ());
    fresh (h t s' t' max) ( ?&[
      (l' === max % t');
      (minmaxo h s' s max);
      (smallesto_rev t s' t');
      (l === h % t);
    ])
  ]

let rec smallesto_rev_wrapped l s l' = relation "smallesto_rev" [!!! l; !!! s; !!! l'] @@
  let open Std in
  conde [
    (l === !< s) &&& (l' === Std.List.nil ());
    fresh (h t s' t' max) ( ?&[
      (l' === max % t');
      (minmaxo_wrapped h s' s max);
      (smallesto_rev_wrapped t s' t');
      (l === h % t);
    ])
  ]

let rec sorto_dir xs ys =
  let open Std in
  conde [
    (xs === Std.List.nil ()) &&& (ys === Std.List.nil ());
    fresh (s xs' ys') (?& [
      (smallesto_dir xs s xs');
      (sorto_dir xs' ys');
      (ys === s % ys');
    ])
  ]

let rec sorto_dir_wrapped xs ys = relation "sorto_dir" [!!! xs; !!! ys] @@
  let open Std in
  conde [
    (xs === Std.List.nil ()) &&& (ys === Std.List.nil ());
    fresh (s xs' ys') (?& [
      (smallesto_dir_wrapped xs s xs');
      (sorto_dir_wrapped xs' ys');
      (ys === s % ys');
    ])
  ]

let rec sorto_rev xs ys =
  let open Std in
  conde [
    (xs === Std.List.nil ()) &&& (ys === Std.List.nil ());
    fresh (s xs' ys') (?& [
      (ys === s % ys');
      (sorto_rev xs' ys');
      (smallesto_rev xs s xs');
    ])
  ]

let rec sorto_rev_wrapped xs ys = relation "sorto_rev" [!!! xs; !!! ys] @@
  let open Std in
  conde [
    (xs === Std.List.nil ()) &&& (ys === Std.List.nil ());
    fresh (s xs' ys') (?& [
      (ys === s % ys');
      (sorto_rev_wrapped xs' ys');
      (smallesto_rev_wrapped xs s xs');
    ])
  ]

let permo_dir xs ys =
  fresh (ss)
    ((sorto_dir xs ss) &&& (sorto_rev ys ss))

let permo_dir_wrapped xs ys = relation "permo_dir" [!!! xs; !!! ys] @@
  fresh (ss)
    ((sorto_dir_wrapped xs ss) &&& (sorto_rev_wrapped ys ss))

let permo_rev xs ys =
  fresh (ss)
    ((sorto_dir ys ss) &&& (sorto_rev xs ss))

let permo_rev_wrapped xs ys = relation "permo_rev" [!!! xs; !!! ys] @@
  fresh (ss)
    ((sorto_dir_wrapped ys ss) &&& (sorto_rev_wrapped xs ss))


(* Binary  arithmetic *)

let bin_poso x =
  let open Std in
  fresh (h t) (x === h % t)

let rec bin_pluso_dir x y r =
  let open Std in
  conde [
    (y === Std.List.nil ()) &&& (x === r);
    (x === Std.List.nil ()) &&& (bin_poso y) &&& (y === r);
    fresh (x' y' r') (?& [
      (x === !0 % x');
      (y === !0 % y');
      (r === !0 % r');
      (bin_poso x');
      (bin_poso y');
      (bin_pluso_dir x' y' r');
    ]);
    fresh (x' y' r') (?& [
      (x === !0 % x');
      (y === !1 % y');
      (r === !1 % r');
      (bin_poso x');
      (bin_pluso_dir x' y' r');
    ]);
    fresh (x' y' r') (?& [
      (x === !1 % x');
      (y === !0 % y');
      (r === !1 % r');
      (bin_poso y');
      (bin_pluso_dir x' y' r');
    ]);
    fresh (x' y' r' r'') (?& [
      (x === !1 % x');
      (y === !1 % y');
      (r === !0 % r');
      (bin_pluso_dir x' y' r'');
      (bin_pluso_dir r'' (!< (!1)) r');
    ])
  ]

let rec bin_pluso_dir_wrapped x y r = relation "bin_pluso_dir" [!!! x; !!! y; !!! r] @@
  let open Std in
  conde [
    (y === Std.List.nil ()) &&& (x === r);
    (x === Std.List.nil ()) &&& (bin_poso y) &&& (y === r);
    fresh (x' y' r') (?& [
      (x === !0 % x');
      (y === !0 % y');
      (r === !0 % r');
      (bin_poso x');
      (bin_poso y');
      (bin_pluso_dir_wrapped x' y' r');
    ]);
    fresh (x' y' r') (?& [
      (x === !0 % x');
      (y === !1 % y');
      (r === !1 % r');
      (bin_poso x');
      (bin_pluso_dir_wrapped x' y' r');
    ]);
    fresh (x' y' r') (?& [
      (x === !1 % x');
      (y === !0 % y');
      (r === !1 % r');
      (bin_poso y');
      (bin_pluso_dir_wrapped x' y' r');
    ]);
    fresh (x' y' r' r'') (?& [
      (x === !1 % x');
      (y === !1 % y');
      (r === !0 % r');
      (bin_pluso_dir_wrapped x' y' r'');
      (bin_pluso_dir_wrapped r'' (!< (!1)) r');
    ])
  ]

let rec bin_pluso_rev x y r =
  let open Std in
  conde [
    (y === Std.List.nil ()) &&& (x === r);
    (x === Std.List.nil ()) &&& (bin_poso y) &&& (y === r);
    fresh (x' y' r') (?& [
      (x === !0 % x');
      (y === !0 % y');
      (r === !0 % r');
      (bin_poso x');
      (bin_poso y');
      (bin_pluso_rev x' y' r');
    ]);
    fresh (x' y' r') (?& [
      (x === !0 % x');
      (y === !1 % y');
      (r === !1 % r');
      (bin_poso x');
      (bin_pluso_rev x' y' r');
    ]);
    fresh (x' y' r') (?& [
      (x === !1 % x');
      (y === !0 % y');
      (r === !1 % r');
      (bin_poso y');
      (bin_pluso_rev x' y' r');
    ]);
    fresh (x' y' r' r'') (?& [
      (x === !1 % x');
      (y === !1 % y');
      (r === !0 % r');
      (bin_pluso_rev r'' (!< (!1)) r');
      (bin_pluso_rev x' y' r'');
    ])
  ]

let rec bin_pluso_rev_wrapped x y r = relation "bin_pluso_rev" [!!! x; !!! y; !!! r] @@
  let open Std in
  conde [
    (y === Std.List.nil ()) &&& (x === r);
    (x === Std.List.nil ()) &&& (bin_poso y) &&& (y === r);
    fresh (x' y' r') (?& [
      (x === !0 % x');
      (y === !0 % y');
      (r === !0 % r');
      (bin_poso x');
      (bin_poso y');
      (bin_pluso_rev_wrapped x' y' r');
    ]);
    fresh (x' y' r') (?& [
      (x === !0 % x');
      (y === !1 % y');
      (r === !1 % r');
      (bin_poso x');
      (bin_pluso_rev_wrapped x' y' r');
    ]);
    fresh (x' y' r') (?& [
      (x === !1 % x');
      (y === !0 % y');
      (r === !1 % r');
      (bin_poso y');
      (bin_pluso_rev_wrapped x' y' r');
    ]);
    fresh (x' y' r' r'') (?& [
      (x === !1 % x');
      (y === !1 % y');
      (r === !0 % r');
      (bin_pluso_rev_wrapped r'' (!< (!1)) r');
      (bin_pluso_rev_wrapped x' y' r'');
    ])
  ]

let rec bin_multo_dir x y r =
  let open Std in
  conde [
    (x === Std.List.nil ()) &&& (r === Std.List.nil ());
    (bin_poso x) &&& (y === Std.List.nil ()) &&& (r === Std.List.nil ());
    (bin_poso x) &&& (y === !< !1) &&& (r === x);
    fresh (y' r') (?& [
      (bin_poso x);
      (y === !0 % y');
      (bin_poso y');
      (bin_multo_dir x y' r');
      (r === !0 % r');
    ]);
    fresh (y' r' r'') (?& [
      (bin_poso x);
      (y === !1 % y');
      (bin_poso y');
      (bin_multo_dir x y' r');
      (r'' === !0 % r');
      (bin_pluso_dir r'' x r);
    ])
  ]

let rec bin_multo_dir_wrapped x y r = relation "bin_multo_dir" [!!! x; !!! y; !!! r] @@
  let open Std in
  conde [
    (x === Std.List.nil ()) &&& (r === Std.List.nil ());
    (bin_poso x) &&& (y === Std.List.nil ()) &&& (r === Std.List.nil ());
    (bin_poso x) &&& (y === !< !1) &&& (r === x);
    fresh (y' r') (?& [
      (bin_poso x);
      (y === !0 % y');
      (bin_poso y');
      (bin_multo_dir_wrapped x y' r');
      (r === !0 % r');
    ]);
    fresh (y' r' r'') (?& [
      (bin_poso x);
      (y === !1 % y');
      (bin_poso y');
      (bin_multo_dir_wrapped x y' r');
      (r'' === !0 % r');
      (bin_pluso_dir_wrapped r'' x r);
    ])
  ]

let rec bin_multo_rev x y r =
  let open Std in
  conde [
    (x === Std.List.nil ()) &&& (r === Std.List.nil ());
    (bin_poso x) &&& (y === Std.List.nil ()) &&& (r === Std.List.nil ());
    (bin_poso x) &&& (y === !< !1) &&& (r === x);
    fresh (y' r') (?& [
      (bin_poso x);
      (bin_poso y');
      (r === !0 % r');
      (bin_multo_rev x y' r');
      (y === !0 % y');
    ]);
    fresh (y' r' r'') (?& [
      (bin_poso x);
      (bin_poso y');
      (r'' === !0 % r');
      (bin_pluso_rev r'' x r);
      (bin_multo_rev x y' r');
      (y === !1 % y');
    ])
  ]

let rec bin_multo_rev_wrapped x y r = relation "bin_multo_rev" [!!! x; !!! y; !!! r] @@
  let open Std in
  conde [
    (x === Std.List.nil ()) &&& (r === Std.List.nil ());
    (bin_poso x) &&& (y === Std.List.nil ()) &&& (r === Std.List.nil ());
    (bin_poso x) &&& (y === !< !1) &&& (r === x);
    fresh (y' r') (?& [
      (bin_poso x);
      (bin_poso y');
      (r === !0 % r');
      (bin_multo_rev_wrapped x y' r');
      (y === !0 % y');
    ]);
    fresh (y' r' r'') (?& [
      (bin_poso x);
      (bin_poso y');
      (r'' === !0 % r');
      (bin_pluso_rev_wrapped r'' x r);
      (bin_multo_rev_wrapped x y' r');
      (y === !1 % y');
    ])
  ]

let bin_lto x y =
  fresh (d) (?& [
    (bin_poso d);
    (bin_pluso_rev x d y)
  ])

let bin_lto_wrapped x y = relation "bin_lto" [!!! x; !!! y] @@
  fresh (d) (?& [
    (bin_poso d);
    (bin_pluso_rev_wrapped x d y)
  ])

let bin_divo_dir x y q' r =
  fresh (z) (?& [
    (bin_lto r y);
    (bin_multo_dir q' y z);
    (bin_pluso_dir z r x);
  ])

let bin_divo_dir_wrapped x y q' r = relation "bin_divo_dir" [!!! x; !!! y] @@
  fresh (z) (?& [
    (bin_lto_wrapped r y);
    (bin_multo_dir_wrapped q' y z);
    (bin_pluso_dir_wrapped z r x);
  ])

let bin_divo_rev x y q' r =
  fresh (z) (?& [
    (bin_pluso_rev z r x);
    (bin_multo_rev q' y z);
    (bin_lto r y);
  ])


(*** Binary trees ***)

let rec leaveso_dir t n =
  let open Std in
  conde [
    (t === leaf) &&& (n === !< (!1));
    fresh (lt ln rt rn) (?& [
      (bin_poso ln);
      (bin_poso rn);
      (t === (node (lt, rt)));
      (leaveso_dir lt ln);
      (leaveso_dir rt rn);
      (bin_pluso_dir ln rn n);
    ])
  ]

let rec leaveso_dir_wrapped t n = relation "leaveso_dir" [!!! t; !!! n] @@
  let open Std in
  conde [
    (t === leaf) &&& (n === !< (!1));
    fresh (lt ln rt rn) (?& [
      (bin_poso ln);
      (bin_poso rn);
      (t === (node (lt, rt)));
      (leaveso_dir_wrapped lt ln);
      (leaveso_dir_wrapped rt rn);
      (bin_pluso_dir_wrapped ln rn n);
    ])
  ]

let rec leaveso_rev t n =
  let open Std in
  conde [
    (t === leaf) &&& (n === !< (!1));
    fresh (lt ln rt rn) (?& [
      (bin_poso ln);
      (bin_poso rn);
      (bin_pluso_rev ln rn n);
      (leaveso_rev lt ln);
      (leaveso_rev rt rn);
      (t === node (lt,rt));
    ])
  ]


let rec rnats = function
| 0 -> []
| n -> n :: rnats (n - 1)

let nats n = List.rev (rnats n)

let show_int      = show(logic) (show int)
let show_int_list = show(Std.List.logic) show_int
let show_nat_list = show(Std.List.logic) (show Std.Nat.logic)
let show_tree     = show(logic) (show tree)

let run_int_list eta =
  runR Std.(List.reify OCanren.reify)
    (show Std.List.ground (show GT.int))
    (show Std.List.logic (show logic @@ show GT.int))
    eta

let run_nat_list eta =
  runR Std.(List.reify Nat.reify)
    (show Std.List.ground (show Std.Nat.ground))
    (show Std.List.logic (show Std.Nat.logic))
    eta

let run_tree eta = runR tree_reify (GT.show tree) (GT.show ltree) eta

let _ = ();
  (*** appendo <= ***)

  (** ) run show_int_list 101 qr (REPR (fun q r -> appendo_rev q r (Std.list (!) (nats 100)))) qrh; ( **)
  (** ) run show_int_list 201 qr (REPR (fun q r -> appendo_rev q r (Std.list (!) (nats 200)))) qrh; ( **)
  (** ) run show_int_list 301 qr (REPR (fun q r -> appendo_rev q r (Std.list (!) (nats 300)))) qrh; ( **)

  (** ) run show_int_list 101 qr (REPR (fun q r -> appendo_dir q r (Std.list (!) (nats 100)))) qrh; ( **)
  (** ) run show_int_list 201 qr (REPR (fun q r -> appendo_dir q r (Std.list (!) (nats 200)))) qrh; ( **)
  (** ) run show_int_list 301 qr (REPR (fun q r -> appendo_dir q r (Std.list (!) (nats 300)))) qrh; ( **)

  (** ) run show_int_list 101 qr (REPR (fun q r -> appendo_dir_wrapped q r (Std.list (!) (nats 100)))) qrh; ( **)
  (** ) run show_int_list 201 qr (REPR (fun q r -> appendo_dir_wrapped q r (Std.list (!) (nats 200)))) qrh; ( **)
  (** ) run show_int_list 301 qr (REPR (fun q r -> appendo_dir_wrapped q r (Std.list (!) (nats 300)))) qrh; ( **)


  (*** reverso => ***)

  (** ) run show_int_list 1 q (REPR (fun q -> reverso_dir (Std.list (!) (nats 30)) q)) qh; ( **)
  (** ) run show_int_list 1 q (REPR (fun q -> reverso_dir (Std.list (!) (nats 60)) q)) qh; ( **)
  (** ) run show_int_list 1 q (REPR (fun q -> reverso_dir (Std.list (!) (nats 90)) q)) qh; ( **)

  (** ) run show_int_list 1 q (REPR (fun q -> reverso_rev (Std.list (!) (nats 30)) q)) qh; ( **)
  (** ) run show_int_list 1 q (REPR (fun q -> reverso_rev (Std.list (!) (nats 60)) q)) qh; ( **)
  (** ) run show_int_list 1 q (REPR (fun q -> reverso_rev (Std.list (!) (nats 90)) q)) qh; ( **)

  (** ) run show_int_list 1 q (REPR (fun q -> reverso_rev_wrapped (Std.list (!) (nats 30)) q)) qh; ( **)
  (** ) run show_int_list 1 q (REPR (fun q -> reverso_rev_wrapped (Std.list (!) (nats 60)) q)) qh; ( **)
  (** ) run show_int_list 1 q (REPR (fun q -> reverso_rev_wrapped (Std.list (!) (nats 90)) q)) qh; ( **)


  (*** reverso <= ***)

  (** ) run show_int_list 1 q (REPR (fun q -> reverso_rev q (Std.list (!) (nats 30)))) qh; ( **)
  (** ) run show_int_list 1 q (REPR (fun q -> reverso_rev q (Std.list (!) (nats 60)))) qh; ( **)
  (** ) run show_int_list 1 q (REPR (fun q -> reverso_rev q (Std.list (!) (nats 90)))) qh; ( **)

  (** ) run show_int_list 1 q (REPR (fun q -> reverso_dir q (Std.list (!) (nats 30)))) qh; ( **)
  (** ) run show_int_list 1 q (REPR (fun q -> reverso_dir q (Std.list (!) (nats 60)))) qh; ( **)
  (** ) run show_int_list 1 q (REPR (fun q -> reverso_dir q (Std.list (!) (nats 90)))) qh; ( **)

  (** ) run show_int_list 1 q (REPR (fun q -> reverso_dir_wrapped q (Std.list (!) (nats 30)))) qh; ( **)
  (** ) run show_int_list 1 q (REPR (fun q -> reverso_dir_wrapped q (Std.list (!) (nats 60)))) qh; ( **)
  (** ) run show_int_list 1 q (REPR (fun q -> reverso_dir_wrapped q (Std.list (!) (nats 90)))) qh; ( **)


  (*** sorto => ***)

  (** ) run show_nat_list 1 q (REPR (fun q -> sorto_dir (inj_nat_list (rnats 2)) q)) qh; ( **)
  (** ) run show_nat_list 1 q (REPR (fun q -> sorto_dir (inj_nat_list (rnats 3)) q)) qh; ( **)
  (** ) run show_nat_list 1 q (REPR (fun q -> sorto_dir (inj_nat_list (rnats 4)) q)) qh; ( **)
  (** ) run show_nat_list 1 q (REPR (fun q -> sorto_dir (inj_nat_list (rnats 10)) q)) qh; ( **)
  (** ) run show_nat_list 1 q (REPR (fun q -> sorto_dir (inj_nat_list (rnats 20)) q)) qh; ( **)
  (** ) run show_nat_list 1 q (REPR (fun q -> sorto_dir (inj_nat_list (rnats 30)) q)) qh; ( **)

  (** ) run show_nat_list 1 q (REPR (fun q -> sorto_rev (inj_nat_list (rnats 2)) q)) qh; ( **)
  (** ) run show_nat_list 1 q (REPR (fun q -> sorto_rev (inj_nat_list (rnats 3)) q)) qh; ( **)
  (** ) run show_nat_list 1 q (REPR (fun q -> sorto_rev (inj_nat_list (rnats 4)) q)) qh; ( **)
  (** ) run show_nat_list 1 q (REPR (fun q -> sorto_rev (inj_nat_list (rnats 20)) q)) qh; ( **)
  (** ) run show_nat_list 1 q (REPR (fun q -> sorto_rev (inj_nat_list (rnats 40)) q)) qh; ( **)

  (** ) run show_nat_list 1 q (REPR (fun q -> sorto_rev_wrapped (inj_nat_list (rnats 2)) q)) qh; ( **)
  (** ) run show_nat_list 1 q (REPR (fun q -> sorto_rev_wrapped (inj_nat_list (rnats 3)) q)) qh; ( **)
  (** ) run show_nat_list 1 q (REPR (fun q -> sorto_rev_wrapped (inj_nat_list (rnats 4)) q)) qh; ( **)
  (** ) run show_nat_list 1 q (REPR (fun q -> sorto_rev_wrapped (inj_nat_list (rnats 10)) q)) qh; ( **)
  (** ) run show_nat_list 1 q (REPR (fun q -> sorto_rev_wrapped (inj_nat_list (rnats 20)) q)) qh; ( **)
  (** ) run show_nat_list 1 q (REPR (fun q -> sorto_rev_wrapped (inj_nat_list (rnats 30)) q)) qh; ( **)


  (*** sorto <= ***)

  (** ) run show_nat_list 2 q (REPR (fun q -> sorto_rev q (inj_nat_list (nats 2)))) qh; ( **)
  (** ) run show_nat_list 6 q (REPR (fun q -> sorto_rev q (inj_nat_list (nats 3)))) qh; ( **)
  (** ) run show_nat_list 24 q (REPR (fun q -> sorto_rev q (inj_nat_list (nats 4)))) qh; ( **)
  (** ) run show_nat_list 120 q (REPR (fun q -> sorto_rev q (inj_nat_list (nats 5)))) qh; ( **)
  (** ) run show_nat_list 720 q (REPR (fun q -> sorto_rev q (inj_nat_list (nats 6)))) qh; ( **)
  (** ) run show_nat_list 5040 q (REPR (fun q -> sorto_rev q (inj_nat_list (nats 7)))) qh; ( **)

  (** ) run show_nat_list 2 q (REPR (fun q -> sorto_dir q (inj_nat_list (nats 2)))) qh; ( **)
  (** ) run show_nat_list 6 q (REPR (fun q -> sorto_dir q (inj_nat_list (nats 3)))) qh; ( **)
  (** ) run show_nat_list 24 q (REPR (fun q -> sorto_dir q (inj_nat_list (nats 4)))) qh; ( **)
  (** ) run show_nat_list 120 q (REPR (fun q -> sorto_dir q (inj_nat_list (nats 5)))) qh; ( **)
  (** ) run show_nat_list 720 q (REPR (fun q -> sorto_dir q (inj_nat_list (nats 6)))) qh; ( **)
  (** ) run show_nat_list 5040 q (REPR (fun q -> sorto_dir q (inj_nat_list (nats 7)))) qh; ( **)

  (** ) run show_nat_list 2 q (REPR (fun q -> sorto_dir_wrapped q (inj_nat_list (nats 2)))) qh; ( **)
  (** ) run show_nat_list 6 q (REPR (fun q -> sorto_dir_wrapped q (inj_nat_list (nats 3)))) qh; ( **)
  (** ) run show_nat_list 24 q (REPR (fun q -> sorto_dir_wrapped q (inj_nat_list (nats 4)))) qh; ( **)
  (** ) run show_nat_list 120 q (REPR (fun q -> sorto_dir_wrapped q (inj_nat_list (nats 5)))) qh; ( **)
  (** ) run show_nat_list 720 q (REPR (fun q -> sorto_dir_wrapped q (inj_nat_list (nats 6)))) qh; ( **)
  (** ) run show_nat_list 5040 q (REPR (fun q -> sorto_dir_wrapped q (inj_nat_list (nats 7)))) qh; ( **)


  (*** permo ***)

  (* run show_nat_list (-1) q (REPR (fun q -> permo_dir (inj_nat_list (rnats 2)) q)) qh; *)
  (** ) run show_nat_list (-1) q (REPR (fun q -> permo_dir (inj_nat_list (rnats 3)) q)) qh; ( **)
  (** ) run show_nat_list (-1) q (REPR (fun q -> permo_dir (inj_nat_list (rnats 4)) q)) qh; ( **)
  (** ) run show_nat_list (-1) q (REPR (fun q -> permo_dir (inj_nat_list (rnats 5)) q)) qh; ( **)
  (** ) run show_nat_list (-1) q (REPR (fun q -> permo_dir (inj_nat_list (rnats 6)) q)) qh; ( **)

  (** ) run show_nat_list 2 q (REPR (fun q -> permo_rev (inj_nat_list (rnats 2)) q)) qh; ( **)
  (** ) run show_nat_list 6 q (REPR (fun q -> permo_rev (inj_nat_list (rnats 3)) q)) qh; ( **)

  (** ) run show_nat_list (-1) q (REPR (fun q -> permo_rev_wrapped (inj_nat_list (rnats 2)) q)) qh; ( **)
  (** ) run show_nat_list (-1) q (REPR (fun q -> permo_rev_wrapped (inj_nat_list (rnats 3)) q)) qh; ( **)
  (** ) run show_nat_list (-1) q (REPR (fun q -> permo_rev_wrapped (inj_nat_list (rnats 4)) q)) qh; ( **)
  (** ) run show_nat_list (-1) q (REPR (fun q -> permo_rev_wrapped (inj_nat_list (rnats 5)) q)) qh; ( **)
  (** ) run show_nat_list (-1) q (REPR (fun q -> permo_rev_wrapped (inj_nat_list (rnats 6)) q)) qh; ( **)


  (* bin_multo <= *)

  (** ) run show_int_list (-1) qr (REPR (fun q r -> bin_multo_rev q r (Std.list (!) [1; 1; 1]))) qrh; ( **)
  (** ) run show_int_list (-1) qr (REPR (fun q r -> bin_multo_rev q r (Std.list (!) [1; 1; 1; 1]))) qrh; ( **)
  (** ) run show_int_list (-1) qr (REPR (fun q r -> bin_multo_rev q r (Std.list (!) [1; 1; 1; 1; 1]))) qrh; ( **)
  (** ) run show_int_list (-1) qr (REPR (fun q r -> bin_multo_rev q r (Std.list (!) [1; 1; 1; 1; 1; 1; 1]))) qrh; ( **)
  (** ) run show_int_list (-1) qr (REPR (fun q r -> bin_multo_rev q r (Std.list (!) [1; 1; 1; 1; 1; 1; 1; 1]))) qrh; ( **)

  (** ) run show_int_list 2 qr (REPR (fun q r -> bin_multo_dir q r (Std.list (!) [1; 1; 1]))) qrh; ( **)
  (** ) run show_int_list 4 qr (REPR (fun q r -> bin_multo_dir q r (Std.list (!) [1; 1; 1; 1]))) qrh; ( **)
  (** ) run show_int_list 2 qr (REPR (fun q r -> bin_multo_dir q r (Std.list (!) [1; 1; 1; 1; 1]))) qrh; ( **)
  (** ) run show_int_list 2 qr (REPR (fun q r -> bin_multo_dir q r (Std.list (!) [1; 1; 1; 1; 1; 1; 1]))) qrh; ( **)
  (** ) run show_int_list 2 qr (REPR (fun q r -> bin_multo_dir q r (Std.list (!) [1; 1; 1; 1; 1; 1; 1; 1]))) qrh; ( **)

  (** ) run show_int_list (-1) qr (REPR (fun q r -> bin_multo_dir_wrapped q r (Std.list (!) [1; 1; 1]))) qrh; ( **)
  (** ) run show_int_list (-1) qr (REPR (fun q r -> bin_multo_dir_wrapped q r (Std.list (!) [1; 1; 1; 1]))) qrh; ( **)
  (** ) run show_int_list (-1) qr (REPR (fun q r -> bin_multo_dir_wrapped q r (Std.list (!) [1; 1; 1; 1; 1]))) qrh; ( **)
  (** ) run show_int_list (-1) qr (REPR (fun q r -> bin_multo_dir_wrapped q r (Std.list (!) [1; 1; 1; 1; 1; 1; 1]))) qrh; ( **)
  (** ) run show_int_list (-1) qr (REPR (fun q r -> bin_multo_dir_wrapped q r (Std.list (!) [1; 1; 1; 1; 1; 1; 1; 1]))) qrh; ( **)


  (*** bin_divo ***)

  run_int_list (-1) qrs qrsh (REPR (fun q r s -> bin_poso r &&& bin_divo_rev (Std.list (!) [0; 0; 1]) q r s));
  (** ) run show_int_list (-1) qrs (REPR (fun q r s -> bin_poso r &&& bin_divo_rev (Std.list (!) [0; 0; 0; 1]) q r s)) qrsh; ( **)
  (** ) run show_int_list (-1) qrs (REPR (fun q r s -> bin_poso r &&& bin_divo_rev (Std.list (!) [0; 0; 0; 0; 1]) q r s)) qrsh; ( **)

  (** ) run show_int_list 8 qrs (REPR (fun q r s -> bin_poso r &&& bin_divo_dir (Std.list (!) [0; 0; 1]) q r s)) qrsh; ( **)

  (** ) run show_int_list (-1) qrs (REPR (fun q r s -> bin_poso r &&& bin_divo_dir_wrapped (Std.list (!) [0; 0; 0; 1]) q r s)) qrsh; ( **)
  (** ) run show_int_list (-1) qrs (REPR (fun q r s -> bin_poso r &&& bin_divo_dir_wrapped (Std.list (!) [0; 0; 0; 0; 1]) q r s)) qrsh; ( **)



  (*** leaveso ***)

  run_tree (-1) q qh (REPR (fun q -> leaveso_rev q (Std.list (!) [1; 1])));
  (** ) run show_tree (-1) q (REPR (fun q -> leaveso_rev q (Std.list (!) [0; 0; 1]))) qh; ( **)
  (** ) run show_tree (-1) q (REPR (fun q -> leaveso_rev q (Std.list (!) [1; 0; 1]))) qh; ( **)
  (** ) run show_tree (-1) q (REPR (fun q -> leaveso_rev q (Std.list (!) [0; 0; 0; 1]))) qh; ( **)

  (** ) run show_tree 2 q (REPR (fun q -> leaveso_dir q (Std.list (!) [1; 1]))) qh; ( **)
  (** ) run show_tree 5 q (REPR (fun q -> leaveso_dir q (Std.list (!) [0; 0; 1]))) qh; ( **)
  (** ) run show_tree 14 q (REPR (fun q -> leaveso_dir q (Std.list (!) [1; 0; 1]))) qh; ( **)

  (** ) run show_tree (-1) q (REPR (fun q -> leaveso_dir_wrapped q (Std.list (!) [1; 1]))) qh; ( **)
  (** ) run show_tree (-1) q (REPR (fun q -> leaveso_dir_wrapped q (Std.list (!) [0; 0; 1]))) qh; ( **)
  (** ) run show_tree (-1) q (REPR (fun q -> leaveso_dir_wrapped q (Std.list (!) [1; 0; 1]))) qh; ( **)
  (** ) run show_tree (-1) q (REPR (fun q -> leaveso_dir_wrapped q (Std.list (!) [0; 0; 0; 1]))) qh; ( **)
