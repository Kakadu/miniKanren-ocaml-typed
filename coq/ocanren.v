Require Import List.
Require Import Arith.
Require Import Omega.
Import ListNotations.
Require Coq.Lists.ListSet.


Inductive Zip {A B : Type} : list A -> list B -> list (A * B) -> Prop :=
| ZipNil : Zip [] [] []
| ZipCons : forall x xs y ys zs, Zip xs ys zs -> Zip (x::xs) (y::ys) ((x, y)::zs).

Inductive Forall4 {A B C D : Type} (R : A -> B -> C -> D -> Prop) : list A -> list B -> list C -> list D -> Prop :=
| Forall3Nil : Forall4 R [] [] [] []
| Forall3Cons : forall w x y z ws xs ys zs, R w x y z -> Forall4 R ws xs ys zs -> Forall4 R (w::ws) (x::xs) (y::ys) (z::zs).



Inductive var : Type :=
| X : nat -> var.

Lemma var_eq_dec : forall x y: var, {x = y} + {x <> y}.
Proof.
  destruct x. destruct y. destruct (eq_nat_dec n n0).
  + left. f_equal. assumption.
  + right. intros H. inversion H. auto.
Qed.

Definition var_set : Type := ListSet.set var.

Definition union : var_set -> var_set -> var_set := ListSet.set_union var_eq_dec.

Definition intersect : var_set -> var_set -> var_set := ListSet.set_inter var_eq_dec.

Definition diff : var_set -> var_set -> var_set := ListSet.set_diff var_eq_dec.

Definition mem : var -> var_set -> bool := ListSet.set_mem var_eq_dec.

Definition add : var -> var_set -> var_set := ListSet.set_add var_eq_dec.

Definition subset (s : var_set) (S : var_set) : Prop := Forall (fun x => In x S) s.

SearchAbout In.

Lemma subset_trans : forall s1 s2 s3, subset s1 s2 -> subset s2 s3 -> subset s1 s3.
Proof.
  intros. apply Forall_forall. intros.
  assert (forall x : var, In x s1 -> In x s2). { apply Forall_forall. assumption. }
  assert (forall x : var, In x s2 -> In x s3). { apply Forall_forall. assumption. }
  auto.
Qed.

Lemma subset_app_right : forall s1 s2 s3, subset s1 s2 -> subset s1 (s2 ++ s3).
Proof.
  intros. assert (forall x : var, In x s1 -> In x s2).
  { apply Forall_forall. assumption. }
  apply Forall_forall. intros. apply H0 in H1. apply in_or_app. left. assumption.
Qed.

Lemma subset_app_left : forall s1 s2 s3, subset s1 s2 -> subset s1 (s3 ++ s2).
Proof.
  intros. assert (forall x : var, In x s1 -> In x s2).
  { apply Forall_forall. assumption. }
  apply Forall_forall. intros. apply H0 in H1. apply in_or_app. right. assumption.
Qed.

Lemma subset_refl : forall s, subset s s.
Proof. intros. apply Forall_forall. intros. assumption. Qed.



Inductive constructor_name : Type :=
| C : nat -> constructor_name.

Inductive term : Type :=
| Var  : var -> term
| Constr : constructor_name -> list term -> term.

Fixpoint term_height (t : term) : nat :=
  match t with
  | Var _ => 0
  | Constr _ ts => S (fold_right max 0 (map term_height ts))
  end.

Lemma term_induction : forall (P : term -> Prop),
  (forall v, P (Var v)) ->
  (forall ts c, (forall t, In t ts -> P t) -> P (Constr c ts)) ->
  (forall t, P t).
Proof.
  intros. remember (term_height t). generalize dependent Heqn. revert t.
  remember (fun n => forall t : term, n = term_height t -> P t) as PP.
  assert (PP n).
  {
    apply lt_wf_ind. clear n. subst PP. intros. destruct t.
    - apply H.
    - apply H0. clear H0. generalize dependent H1. generalize dependent H2. revert n.
      induction l.
      + intros. inversion H0.
      + intros. inversion H0.
        * subst a. apply H1 with (term_height t).
          { simpl in H2. rewrite H2. apply le_lt_n_Sm. apply Max.le_max_l. }
          { reflexivity. }
        * eapply IHl.
          { reflexivity. }
          {
            intros. apply H1 with m.
            - apply lt_le_trans with (term_height (Constr c l)).
              + assumption.
              + rewrite H2. simpl. apply le_n_S. apply Max.le_max_r.
            - assumption.
          }
          { assumption. }
  }
  subst PP. assumption.
Qed.



Definition subst : Type := list (var * term).

Definition empty_subst : subst := [].

Fixpoint vars (t : term) : var_set :=
  match t with
  | Var x => [x]
  | Constr _ ts => flat_map vars ts
  end.

Definition dom (s : subst) : var_set := map fst s.

Definition v_ran (s : subst) : var_set := flat_map (fun '(_, t) => vars t) s.



Fixpoint lookup (v : var) (s : subst) : option term :=
  match s with
  | [] => None
  | (x, t)::ss => if var_eq_dec x v then Some t else lookup v ss
  end.

Lemma lookup_some_app : forall x y s1 s2,
  lookup x s1 = Some y -> lookup x (s1 ++ s2) = Some y.
Proof.
  intros. induction s1.
  - inversion H.
  - destruct a. simpl. simpl in H. destruct (var_eq_dec v x).
    + assumption.
    + auto.
Qed.

Fixpoint app (t : term) (s : subst) : term :=
  match t with
  | Var x => match lookup x s with
             | None => Var x
             | Some t => t
             end
  | Constr c ts => Constr c (map (fun t => app t s) ts)
  end.



Definition comp (s1 : subst) (s2 : subst) : subst :=
  (map (fun '(x, t) => (x, app t s2)) s1) ++ s2.

Lemma comp_is_composition : forall (t : term) (s1 s2 : subst),
  app t (comp s1 s2) = app (app t s1) s2.
Proof.
  intros. remember (fun t => app t (comp s1 s2) = app (app t s1) s2) as P.
  assert (P t).
  {
    apply term_induction.
    - subst P. intros v. simpl. destruct (lookup v s1) eqn:eql.
      + unfold comp.
        assert (
          lookup v (map (fun '(x, t) => (x, app t s2)) s1 ++ s2) = Some (app t0 s2)
        ).
        { apply lookup_some_app. induction s1.
          - inversion eql.
          - destruct a. simpl in eql. simpl. destruct (var_eq_dec v0 v).
            + inversion eql. reflexivity.
            + apply IHs1. assumption. }
        rewrite H. reflexivity.
      + simpl. assert (lookup v (comp s1 s2) = lookup v s2).
        {
          unfold comp. induction s1.
          - reflexivity.
          - destruct a. simpl in eql. simpl. destruct (var_eq_dec v0 v).
            + inversion eql.
            + apply IHs1. assumption.
        }
        rewrite H. reflexivity.
    - subst P. intros. simpl. apply f_equal. rewrite map_map.
      apply map_ext_in. assumption.
  }
  subst P. assumption.
Qed.

Lemma empty_subst_id_right : forall (s : subst), comp s empty_subst = s.
Proof.
  intros. unfold empty_subst. unfold comp. rewrite app_nil_r.
  induction s.
  - reflexivity.
  - destruct a. simpl. rewrite IHs.
    replace (app t []) with t.
    + reflexivity.
    + apply term_induction with (P := fun t => t = app t []).
      * intros. reflexivity.
      * intros. simpl. apply f_equal.
        assert (map (fun x => x) ts = map (fun t0 : term => app t0 []) ts).
        { apply map_ext_in. assumption. }
        rewrite map_id in H0. apply H0.
Qed.

Lemma empty_subst_id_left : forall (s : subst), comp empty_subst s = s.
Proof. intros. unfold empty_subst. unfold comp. reflexivity. Qed.

Definition subst_equal (s1 : subst) (s2 : subst) : Prop := forall x, lookup x s1 = lookup x s2.

Definition unifier (t1 : term) (t2 : term) (u : subst) : Prop := app t1 u = app t2 u.

Inductive mgu (t1 : term) (t2 : term) (m : subst) : Prop :=
| MGU : subset (dom m) (union (vars t1) (vars t2)) ->
        subset (v_ran m) (union (vars t1) (vars t2)) ->
        unifier t1 t2 m ->
        (forall (u : subst), unifier t1 t2 u -> exists (w : subst), subst_equal u (comp m w)) ->
        mgu t1 t2 m.



Inductive relation_name :  Type :=
| R : nat -> relation_name.

Inductive goal : Type :=
| Unify : term -> term -> goal
| Disj : goal -> goal -> goal
| Conj : goal -> goal -> goal
| Fresh : var -> goal -> goal
| Invoke : relation_name -> list term -> goal.

Inductive definition : Type :=
| Lam : list var -> goal -> definition.

Definition state : Type := subst * var_set.

Definition defs : Type := relation_name -> definition.

Definition environment : Type := defs * subst.

Definition call_record : Type := relation_name * list term * subst * subst * var_set * nat.

Definition calls_list : Type := list call_record.


Inductive bs_derivation_tree : environment -> state -> goal -> list state -> nat -> calls_list -> Prop :=
| bsUnifyFail : forall G i s d t1 t2,
    subset (vars t1) (dom i) -> subset (vars t2) (dom i) ->
    ~ (exists (m : subst), mgu (app (app t1 i) s) (app (app t2 i) s) m) ->
    bs_derivation_tree (G, i) (s, d) (Unify t1 t2) [] 0 []
| bsUnifySuccess : forall G i s d t1 t2 m,
    subset (vars t1) (dom i) -> subset (vars t2) (dom i) ->
    mgu (app (app t1 i) s) (app (app t2 i) s) m ->
    bs_derivation_tree (G, i) (s, d) (Unify t1 t2) [(comp s m, d)] 0 []
| bsDisj : forall G i s d g1 g2 rs1 rs2 h1 h2 cl1 cl2,
    bs_derivation_tree (G, i) (s, d) g1 rs1 h1 cl1 ->
    bs_derivation_tree (G, i) (s, d) g2 rs2 h2 cl2 ->
    bs_derivation_tree (G, i) (s, d) (Disj g1 g2) (rs1 ++ rs2) (S (max h1 h2)) (cl1 ++ cl2)
| bsConj : forall G i s d g1 g2 rs1 rss h1 hs cl1 cls,
    bs_derivation_tree (G, i) (s, d) g1 rs1 h1 cl1 ->
    Forall4 (fun st rs2 h cl => bs_derivation_tree (G, i) st g2 rs2 h cl) rs1 rss hs cls  ->
    bs_derivation_tree (G, i) (s, d) (Conj g1 g2) (flat_map id rss) (S (fold_right max h1 hs)) (cl1 ++ concat cls)
| bsFresh : forall G i s d x g rs a h cl,
    ~ (In a d) ->
    bs_derivation_tree (G, i) ((x, Var a)::s, add a d) g rs h cl ->
    bs_derivation_tree (G, i) (s, d) (Fresh x g) rs (S h) cl
| bsInvoke : forall G i s d r ts rs xs g vs cs h cl,
    Forall (fun t => subset (vars t) (dom i)) ts ->
    G r = Lam xs g ->
    vs = map (fun t => app (app t i) s) ts ->
    Zip xs vs cs ->
    bs_derivation_tree (G, cs) (empty_subst, d) g rs h cl ->
    bs_derivation_tree (G, i) (s, d) (Invoke r ts) (map (fun p => (comp s (fst p), snd p)) rs) (S h) ((r, ts, i, s, d, S(h))::cl).



Definition reachable_vars (i : subst) (s : subst) : var_set := flat_map (fun '(_, t) => vars (app t s)) i.

Lemma first_lemma : forall G i s d g rs h cl,
  bs_derivation_tree (G, i) (s, d) g rs h cl -> 
  Forall (fun '(sr, dr) => exists (ds : subst) (dd : var_set),
                sr = comp s ds /\
                dr = union d dd /\
                forall v, (In v (dom ds) \/ In v (v_ran ds)) ->
                          (~(In v d) \/ In v (reachable_vars i s))) rs.
Proof. admit. Admitted.



Lemma second_lemma : forall G i i' s s' d d' g rs rs' h h' cl cl',
  dom i = dom i' ->
  subset (dom s) d -> subset (dom s') d' ->
  subset (reachable_vars i s) d -> subset (reachable_vars i' s') d' ->
  bs_derivation_tree (G, i) (s, d) g rs h cl ->
  bs_derivation_tree (G, i') (s', d') g rs' h' cl' ->
  (exists (tau : subst), forall x, In x (dom i) ->
    app (app (Var x) i') s' = app (app (app (Var x) i) s) tau
  ) ->
  (forall sr' dr', In (sr', dr') rs' ->
    exists sr dr taur, In (sr, dr) rs /\
      forall x, In x (dom i) ->
        app (app (Var x) i') sr' = app (app (app (Var x) i) sr) taur
  ) /\ h >= h'.
Proof. admit. Admitted.



Lemma third_lemma : forall G i s d r ts rs h nr cl,
  subset (reachable_vars i s) d ->
  bs_derivation_tree (G, i) (s, d) (Invoke r ts) rs h (nr::cl) ->
  Forall (fun '(r', ts', i', s', d', h') => exists cl' rs',
                    subset (reachable_vars i' s') d' /\
                    bs_derivation_tree (G, i') (s', d') (Invoke r' ts') rs' h' cl' /\
                    h > h') cl.
Proof. admit. Admitted.



Definition more_general (gts sts : list term) : Prop := exists (s : subst), Forall2 (fun gt st => app gt s = st) gts sts.

Lemma Forall_app : forall (A : Type) (P : A -> Prop) (xs ys : list A),
  Forall P xs -> Forall P ys -> Forall P (xs ++ ys).
Proof.
  induction xs.
  - intros. assumption.
  - intros. inversion H. simpl. constructor.
    + assumption.
    + apply IHxs; assumption.
Qed.

Lemma Forall_app_left : forall (A : Type) (P : A -> Prop) (xs ys : list A),
   Forall P (xs ++ ys) -> Forall P xs.
Proof.
  intros A P xs ys. induction xs.
  - intros. constructor.
  - intros. simpl in H. inversion H. constructor.
    + assumption.
    + apply IHxs. assumption.
Qed.

Lemma Forall_app_right : forall (A : Type) (P : A -> Prop) (xs ys : list A),
   Forall P (xs ++ ys) -> Forall P ys.
Proof.
  intros A P xs ys. induction xs.
  - intros. assumption.
  - intros. simpl in H. inversion H. apply IHxs. assumption.
Qed.

Theorem divergence_criterion : forall G i s d r ts rs h nr cl,
  subset (reachable_vars i s) d ->
  bs_derivation_tree (G, i) (s, d) (Invoke r ts) rs h (nr::cl) ->
  Forall (fun '(r', ts', i', s', _, _) => ~ (r' = r /\ more_general (map (fun t' => app (app t' i') s') ts')
                                                                    (map (fun t  => app (app t  i ) s ) ts ))) cl.
Proof.
  intros. apply Forall_forall. intros c inH. destruct c as [[[[[r' ts'] i'] s'] d'] h'] eqn:eqc.
  rewrite <- eqc in inH. intros cH. destruct cH. subst r'.
  assert (let '(r, ts', i', s', d', h') := c in exists cl' rs',
                  subset (reachable_vars i' s') d' /\
                  bs_derivation_tree (G, i') (s', d') (Invoke r ts') rs' h' cl' /\
                  h > h').
  { generalize dependent inH. clear eqc. generalize dependent c.
    apply Forall_forall. eapply third_lemma. eassumption. eassumption. }
  subst.  destruct H1 as [cl' [rs' [H1 [H3 H4]]]].
  inversion H0. subst. clear H0. inversion H3. subst. clear H3.
  assert (forall ts i s d xs cs, 
             subset (reachable_vars i s) d ->
             Forall (fun t : term => subset (vars t) (dom i)) ts ->
             Zip xs (map (fun t : term => app (app t i) s) ts) cs ->
             subset (reachable_vars cs empty_subst) d) as case34L.
  {
    clear. intros ts i s d xs cs isH. revert cs ts. induction xs.
    - intros. inversion H0. constructor.
    - intros. inversion H0. subst. destruct ts as [| t ts'].
      + inversion H4.
      + inversion H4. subst. clear H4. unfold reachable_vars. simpl.
        inversion H. subst. clear H. unfold subset. apply Forall_app.
        * clear H4 H5 H0 zs ts' IHxs a.
          assert (subset (vars (app (app (app t i) s) empty_subst)) (reachable_vars i s)).
          {
            rewrite <- comp_is_composition. rewrite empty_subst_id_right.
            clear isH. generalize dependent H3.
            apply term_induction with (P := fun t => subset (vars t) (dom i) ->
                        subset (vars (app (app t i) s))
                               (reachable_vars i s)).
            - intros. inversion H. subst. clear H H3. induction i.
              + inversion H2.
              + destruct a. simpl. destruct (var_eq_dec v0 v).
                * apply subset_app_right. apply subset_refl.
                * apply subset_app_left. apply IHi. inversion H2.
                  { simpl in H. exfalso. apply n. assumption. }
                  { assumption. }
            - intros. simpl. simpl in H0. generalize dependent H.
              generalize dependent H0. induction ts.
              + intros. simpl. constructor.
              + intros. simpl. apply Forall_app.
                * apply H.
                  { constructor. reflexivity. }
                  { simpl in H0. apply Forall_app_left in H0. assumption. }
                * apply IHts.
                  { simpl in H0. apply Forall_app_right in H0. assumption. }
                  { intros. apply H.
                    - simpl. right. assumption.
                    - assumption. }
          }
          eapply subset_trans. eassumption. eassumption.
        * apply IHxs with ts'. assumption. assumption.
  }
  rewrite H16 in H11. clear H16. inversion H11. subst. clear H11. assert (h >= h0).
  {
    eapply proj2. eapply second_lemma.
    - assert (dom cs0 = dom cs) as asH.
      {
        generalize dependent H18. remember (map (fun t : term => app (app t i) s) ts) as tr.
        generalize dependent H20. remember (map (fun t : term => app (app t i') s') ts') as tr0.
        clear. revert tr tr0 cs cs0. induction xs0.
        - intros. inversion H18. inversion H20. reflexivity.
        - intros. inversion H18. inversion H20. simpl. apply f_equal. eapply IHxs0.
          eassumption. eassumption.
      }
      eapply asH.
    - assert (subset (dom empty_subst) d'). { unfold subset. constructor. } eapply H0.
    - assert (subset (dom empty_subst) d). { unfold subset. constructor. } eapply H0.
    - apply case34L with ts' i' s' xs0. assumption. assumption. assumption.
    - apply case34L with ts i s xs0. assumption. assumption. assumption.
    - eassumption.
    - eassumption.
    - unfold more_general in H2. destruct H2 as [tau tauH]. exists tau.
      intros. rewrite <- comp_is_composition. rewrite empty_subst_id_right.
      assert (app (app (Var x) cs0) empty_subst = app (Var x) cs0).
      { rewrite <- comp_is_composition. rewrite empty_subst_id_right. reflexivity. }
      rewrite H2. clear H2. generalize dependent H0. revert x. generalize dependent H20.
      generalize dependent H18. generalize dependent tauH. clear. revert ts ts' cs cs0.
      induction xs0.
      + intros. inversion H18. inversion H20. subst. inversion H0.
      + intros. inversion H18. inversion H20. subst. clear H18 H20.
        destruct ts as [| t ts]; inversion H3. destruct ts' as [| t' ts']; inversion H8.
        clear H3 H8. subst. simpl. destruct (var_eq_dec a x).
        * inversion tauH. subst. clear tauH. symmetry. assumption.
        * apply IHxs0 with ts ts'.
          { inversion tauH. subst. clear tauH. assumption. }
          { assumption. }
          { assumption. }
          {
            destruct H0.
            - simpl in H. exfalso. apply n. assumption.
            - assumption.
          }
  }
  omega.
Qed.


