(** Call by value semantics with memoisation **)
Require Import Omega Psatz.
Require Import Bool Arith Compare_dec Max List Permutation.
Import List.ListNotations.
Require Import Cecoa.Lib Cecoa.Syntax.

Set Implicit Arguments.
Unset Strict Implicit.

Section CBV.

Variables variable function constructor : Type.

Variable variable_eq_dec : forall (x1 x2 : variable), {x1=x2}+{x1<>x2}.

Variable function_eq_dec : forall (x1 x2 : function), {x1=x2}+{x1<>x2}.

Variable constructor_eq_dec : forall (x1 x2 : constructor), {x1=x2}+{x1<>x2}.

Notation value := (Syntax.value constructor).
Notation term := (Syntax.term variable function constructor).
Notation pattern := (Syntax.pattern variable constructor).
Notation rule := (Syntax.rule variable function constructor).
Notation term_beq := (term_beq variable_eq_dec function_eq_dec constructor_eq_dec).
Notation "'╎' t '╎'" := (@term_size variable function constructor t) (at level 10).

(** Cache as association list **)
Definition cache : Type := list (term * value).

Notation assoc_cache := (assoc term_beq).

Definition cache_beq (C C' : cache) : bool :=
  list_beq _ (prod_beq _ _ term_beq (value_beq constructor_eq_dec)) C C'.

Lemma cache_beq_eq c1 c2 : cache_beq c1 c2 = true <-> c1 = c2.
Proof.
unfold cache_beq.
apply list_beq_eq.
intros; apply prod_beq_eq.
intros; apply term_beq_eq; trivial.
intros; apply value_beq_eq; trivial.
Qed.

Lemma function_beq_refl (f : function) :
  forall p, function_beq p f f = true.
Proof.
intros; rewrite function_beq_eq; trivial.
Qed.

Lemma value_beq_refl (v : value) :
  value_beq constructor_eq_dec v v = true.
Proof.
apply value_beq_eq; trivial.
Qed.

Lemma cache_beq_refl C :
  cache_beq C C = true.
Proof.
apply cache_beq_eq; trivial.
Qed.

(** * Derivation rules *)
Inductive cbv : Type :=
| cbv_constr : list cbv -> cache -> term -> cache -> value -> cbv
| cbv_split : list cbv -> cbv -> cache -> term -> cache -> value -> cbv
| cbv_update : nat -> (variable -> value) -> cbv -> cache -> term -> cache -> value -> cbv
| cbv_read : cache -> term -> value -> cbv.

(* begin hide *)
Lemma cbv_ind2_gen :
  forall (P : cbv -> Prop)(Q : list cbv -> Prop),
  Q nil ->
  (forall p lp, P p -> Q lp -> Q (p :: lp)) ->
  (forall lp c1 t c2 v, Q lp -> P (cbv_constr lp c1 t c2 v)) ->
  (forall lp p c1 t c2 v, Q lp -> P p -> P (cbv_split lp p c1 t c2 v)) ->
  (forall n s p c1 t c2 v, P p -> P (cbv_update n s p c1 t c2 v)) ->
  (forall c t v, P (cbv_read c t v)) ->
  forall p, P p.
Proof.
fix H1 9; intros P Q H2 H3 H4 H5 H6 H7 [ lp c1 t c2 v | lp p c1 t c2 v | n s p c1 t c2 v | c t v ];
pose (H1 P Q) as HH1.

- apply H4; revert lp; fix H8 1; intros [ | p lp];
  try apply H3; auto.

- apply H5; revert lp; fix H8 1; intros [ | p' lp];
  try apply H3; auto.

- auto.

- auto.

Qed.
(* end hide *)

(** Smarter induction principle than the one automatically generated *)

Lemma cbv_ind2 :
  forall (P : cbv -> Prop),
  (forall lp c1 t c2 v, (forall p, In p lp -> P p) -> P (cbv_constr lp c1 t c2 v)) ->
  (forall lp p c1 t c2 v, (forall p, In p lp -> P p) -> P p -> P (cbv_split lp p c1 t c2 v)) ->
  (forall n s p c1 t c2 v, P p -> P (cbv_update n s p c1 t c2 v)) ->
  (forall c t v, P (cbv_read c t v)) ->
  forall p, P p.
Proof.
intros P H1 H2 H3 H4 p.
apply cbv_ind2_gen with (Q := fun lp => forall p, In p lp -> P p); simpl; try tauto.
intuition; subst; trivial.
Qed.

(** Being a subtree of **)

Fixpoint InCBV p π : Prop :=
  p = π \/
  match π with
      | cbv_constr lp _ _ _ _ => orl (map (InCBV p) lp)
      | cbv_split lp p' _ _ _ _ => InCBV p p' \/ orl (map (InCBV p) lp)
      | cbv_update _ _ p' _ _ _ _ => InCBV p p'
      | cbv_read _ _ _ => False
  end.

Lemma InCBV_refl p : InCBV p p.
Proof.
induction p using cbv_ind2; simpl; tauto.
Qed.

Lemma InCBV_trans p p' p'': InCBV p p' -> InCBV p' p'' -> InCBV p p''.
Proof.
revert p p'.
induction p'' as [lp c1 t c2 v IH_lp | lp p1 c1 t c2 v IH_lp IH_p' | i s p1 c1 t c2 v IH_p' | c t v] using cbv_ind2;
intros p p' H1 [H2 | H2]; simpl; subst; trivial.

- right.
  rewrite orl_map in *.
  destruct H2 as (p1 & H2 & H3).
  exists p1.
  split; trivial.
  apply IH_lp with p'; trivial.

- destruct H2 as [H2 | H2].

  + right.
    left.
    apply IH_p' with p'; trivial.

  + right.
    right.
    rewrite orl_map in *.
    destruct H2 as (p2 & H2 & H3).
    exists p2.
    split; trivial.
    apply IH_lp with p'; trivial.

- right.
  apply IH_p' with p'; trivial.

- tauto.
Qed.

(** Reverse induction on proof trees *)

Lemma cbv_reverse_induction :
  forall (P : cbv -> Prop) π,
  P π ->
  (forall lp c1 t c2 v, InCBV (cbv_constr lp c1 t c2 v) π -> P (cbv_constr lp c1 t c2 v) -> forall p, In p lp -> P p) ->
  (forall lp p c1 t c2 v, InCBV (cbv_split lp p c1 t c2 v) π -> P (cbv_split lp p c1 t c2 v) -> forall p', (p' = p \/ In p' lp) -> P p') ->
  (forall i s p c1 t c2 v, InCBV (cbv_update i s p c1 t c2 v) π -> P (cbv_update i s p c1 t c2 v) -> P p) ->
  forall p, InCBV p π -> P p.
Proof.
intros P π H_π H_constr H_split H_function p H_p.
induction π as [lp c1 t c2 v IH_lp | lp p' c1 t c2 v IH_lp IH_p' | i s p' c1 t c2 v IH_p' | c t v] using cbv_ind2;
simpl in H_p.

- destruct H_p as [H_p | H_p].

  + congruence.

  + apply orl_map in H_p.
    destruct H_p as [p' [H1 H2] ].
    apply IH_lp with p'; trivial.

    * { eapply H_constr.

      - apply InCBV_refl.

      - exact H_π.

      - exact H1. }

    * intros lp' c1' t' c2' v' H3 H4 p'' H5.
      apply H_constr with lp' c1' t' c2' v'; trivial.
      simpl.
      right.
      apply orl_map.
      exists p'.
      tauto.

    * intros lp' p'' c1' t' c2' v' H3 H4 p''' H5.
      apply H_split with lp' p'' c1' t' c2' v'; trivial.
      simpl.
      right.
      apply orl_map.
      exists p'.
      tauto.

    * intros i s p'' c1' t' c2' v' H3 H4.
      apply H_function with i s c1' t' c2' v'; trivial.
      simpl.
      right.
      apply orl_map.
      exists p'.
      tauto.

- destruct H_p as [H_p | [H_p | H_p] ].

  + congruence.

  + apply IH_p'.

    * { eapply H_split.

      - apply InCBV_refl.

      - exact H_π.

      - left; reflexivity. }

    * intros lp' c1' t' c2' v' H3 H4 p'' H5.
      apply H_constr with lp' c1' t' c2' v'; trivial.
      simpl; tauto.

    * intros lp' p'' c1' t' c2' v' H3 H4 p''' H5.
      apply H_split with lp' p'' c1' t' c2' v'; trivial.
      simpl; tauto.

    * intros i s p'' c1' t' c2' v' H3 H4.
      apply H_function with i s c1' t' c2' v'; trivial.
      simpl; tauto.

    * exact H_p.

  + apply orl_map in H_p.
    destruct H_p as [p'' [H1 H2] ].
    apply IH_lp with p''; trivial.
    eapply H_split.

    * apply InCBV_refl.

    * exact H_π.

    *  right; exact H1.

    * intros lp' c1' t' c2' v' H3 H4 p''' H5.
      apply H_constr with lp' c1' t' c2' v'; trivial.
      simpl.
      right; right.
      apply orl_map.
      exists p''.
      tauto.

    * intros lp' p''' c1' t' c2' v' H3 H4 p'''' H5.
      apply H_split with lp' p''' c1' t' c2' v'; trivial.
      simpl.
      right; right.
      apply orl_map.
      exists p''.
      tauto.

    * intros i s p''' c1' t' c2' v' H3 H4.
      apply H_function with i s c1' t' c2' v'; trivial.
      simpl.
      right; right.
      apply orl_map.
      exists p''.
      tauto.

- destruct H_p as [H_p | H_p].

  + congruence.

  + apply IH_p'.

    * { eapply H_function.

      - apply InCBV_refl.

      - exact H_π. }

    * intros lp' c1' t' c2' v' H3 H4 p'' H5.
      apply H_constr with lp' c1' t' c2' v'; trivial.
      simpl; tauto.

    * intros lp' p'' c1' t' c2' v' H3 H4 p''' H5.
      apply H_split with lp' p'' c1' t' c2' v'; trivial.
      simpl; tauto.

    * intros i' s' p'' c1' t' c2' v' H3 H4.
      apply H_function with i' s' c1' t' c2' v'; trivial.
      simpl; tauto.

    * exact H_p.

- destruct H_p as [H_p | H_p].

  + congruence.

  + tauto.
Qed.

Definition rule_subst_of_cbv_update ( subst_default : variable -> value) (π : cbv) : nat * (variable -> value) :=
  match π with
  | cbv_update i s _ _ _ _ _ => (i, s)
  | _ => (0, subst_default) (* impossible case *)
  end.

(** Term of a tree *)
Definition proj_left (π : cbv) : term :=
  match π with
    | cbv_constr _ _ t _ _ => t
    | cbv_split _ _ _ t _ _ => t
    | cbv_update _ _ _ _ t _ _ => t
    | cbv_read _ t _ => t
  end.

(** Value of a tree *)
Definition proj_right (π : cbv) : value :=
  match π with
    | cbv_constr _ _ _ _ v => v
    | cbv_split _ _ _ _ _ v => v
    | cbv_update _ _ _ _ _ _ v => v
    | cbv_read _ _ v => v
  end.

(** * Caches *)

(** Initial cache of a tree*)
Definition cache_left (π : cbv) : cache :=
  match π with
    | cbv_constr _ c _ _ _ => c
    | cbv_split _ _ c _ _ _ => c
    | cbv_update _ _ _ c _ _ _ => c
    | cbv_read c _ _ => c
  end.

(** Final cache of a tree*)
Definition cache_right (π : cbv) : cache :=
  match π with
    | cbv_constr _ _ _ c _ => c
    | cbv_split _ _ _ _ c _ => c
    | cbv_update _ _ _ _ _ c _ => c
    | cbv_read c _ _ => c
  end.

(** When a list of trees form a coherent succession of caches *)
Fixpoint cache_path (C C' : cache)(l : list cbv) : bool :=
  match l with
  | nil => cache_beq C C'
  | p :: l' => cache_beq C (cache_left p) && cache_path (cache_right p) C' l'
  end.

Lemma cache_path_cons c1 c2 p lp :
  cache_path c1 c2 (p :: lp) = true <->
  cache_path c1 (cache_right p) [p] = true /\ cache_path (cache_right p) c2 lp = true.
Proof.
simpl.
do 2 rewrite andb_true_iff.
do 2 rewrite cache_beq_eq.
tauto.
Qed.

Lemma cache_path_app c1 c2 lp p lp' :
  cache_path c1 c2 (lp ++ p :: lp') = true <->
  cache_path c1 (cache_left p) lp = true /\ cache_path (cache_left p) c2 (p :: lp') = true.
Proof.
revert c1.
induction lp as [ | p' lp IH ]; intros c1; simpl; repeat rewrite andb_true_iff; do 2 rewrite cache_beq_eq.

- tauto.

- split.

  + intros [ H1 H2 ].
    apply IH in H2.
    destruct H2 as [ H2 H3 ].
    apply cache_path_cons in H3.
    tauto.

  + intros H1.
    split; try tauto.
    apply IH.
    split; try tauto.
    apply cache_path_cons.
    split; try tauto.
    simpl.
    rewrite andb_true_iff.
    split; rewrite cache_beq_eq; reflexivity.
Qed.

Lemma cache_path_ind (P : cache -> cache -> list cbv -> Prop) C :
  (P C C []) ->
  (forall p lp, cache_path (cache_left p) C (p :: lp) = true -> P (cache_right p) C lp ->
   P (cache_left p) C (p :: lp)) ->
  forall lp C', cache_path C' C lp = true -> P C' C lp.
Proof.
intros H_base H_step lp.
induction lp as [ | p lp IH ]; intros C' H_cache.

- simpl in H_cache.
  apply cache_beq_eq in H_cache; trivial.
  congruence.

- simpl in H_cache.
  apply Bool.andb_true_iff in H_cache.
  destruct H_cache as [Heq H_cache].
  apply cache_beq_eq in Heq; trivial.
  subst C'.
  apply H_step; auto.
  simpl.
  apply Bool.andb_true_iff.
  split; trivial.
  apply cache_beq_eq; trivial.
Qed.

Lemma cache_path_revflatten c1 c2 lp Clp :
  cache_path c1 c2 lp = true ->
  Forall2 (fun p C => cache_right p = C ++ cache_left p) lp Clp ->
  c2 = revflatten Clp ++ c1.
Proof.
revert c1 lp.
induction Clp as [ | Cp Clp' IH ]; intros c1 lp Hpath Hfor2.

- inversion Hfor2; subst.
  simpl in *.
  rewrite cache_beq_eq in Hpath; trivial.
  symmetry; trivial.

- simpl.
  assert (exists p' lp', lp = p' :: lp') as (p' & lp' & Heqlp). {
    inversion Hfor2.
    do 2 eexists.
    tauto.
  }
  rewrite <- app_assoc.
  rewrite IH with (c1 := Cp ++ c1) (lp := lp'); trivial.

  + subst lp.
    inversion Hfor2 as [ | Ba Bb Bc Bd Heqcache Hfor2' ];
    subst.
    simpl in Hpath.
    rewrite Bool.andb_true_iff in Hpath; destruct Hpath as [ Heqc1 Hpath ].
    rewrite cache_beq_eq in Heqc1; trivial; subst c1.
    rewrite <- Heqcache.
    trivial.

  + subst lp.
    inversion Hfor2.
    trivial.
Qed.

Lemma cache_path_transitivity_left c c' l: forall P:cache-> Prop,
      cache_path c c' l = true ->
      P c ->(forall p, In p l ->
      P (cache_left p) ->
      P (cache_right p)) ->
     (forall p, In p l -> P (cache_left p)).
Proof.
revert l c.
induction l.
intros.
simpl in H2;exfalso;auto.
simpl.
intros.
assert (P (cache_right a)).
apply (H1 a).

left;auto.
apply andb_true_iff in H.
elim H;clear H;intros.
apply cache_beq_eq in H.
subst;auto.
elim H2;clear H2;intros.
apply andb_true_iff in H.
elim H;clear H;intros.
apply cache_beq_eq in H.
subst;auto.
apply (IHl (cache_right a));auto.
apply andb_true_iff in H.
elim H;clear H;auto.
Qed.

Lemma cache_path_transitivity c c' l: forall P:cache-> Prop,
      cache_path c c' l = true ->
      P c ->(forall p, In p l ->
      P (cache_left p) ->
      P (cache_right p)) -> P c'.
Proof.
revert l c.
induction l.
intros.
apply cache_beq_eq in H.
rewrite <- H;auto.
intros.
simpl in H.
apply andb_true_iff in H.
elim H;clear H;intros.
apply cache_beq_eq in H.
assert (P (cache_right a)).
apply (H1 a).
simpl;auto.
rewrite H in H0;auto.
apply (IHl (cache_right a));auto.
intros.
assert (In p (a::l));auto.
simpl;auto.
Qed.

Fixpoint cache_lookup (C: cache) (t: term) : term :=
  match t with
  | var _       => t
  | capply c lt => capply c (map (cache_lookup C) lt)
  | fapply f lt => match assoc_cache (fapply f (map (cache_lookup C) lt)) C with
                   | Some v => @term_from_value _ _ _ v
                   | None   => t
                   end
  end.

Lemma cache_lookup_value (C: cache) (v: value):
  let t := @term_from_value _ _ _ v in cache_lookup C t = t.
Proof.
simpl.
induction v as [ c lv IH ] using value_ind2.
induction lv as [ | v lv IH' ]; trivial.
simpl.
rewrite IH; try (simpl; tauto).
do 2 f_equal.
injection IH'; auto with *.
Qed.

Lemma map_cache_lookup_value (C: cache) (lv: list value):
  let lt := map (@term_from_value _ _ _) lv in map (cache_lookup C) lt = lt.
Proof.
induction lv as [ | v lv IH ]; trivial.
simpl.
rewrite cache_lookup_value.
f_equal.
apply IH.
Qed.

Variable rule_default : rule.

Variable prog : list rule.

Variable max_arity : nat.

(** * Well-formed trees *)

Fixpoint wf (π : cbv) : Prop :=
  match π with
    | cbv_constr l C (capply c lt) C' (c_capply c' lv) =>
        cache_path C C' l = true /\
        c = c' /\
        lt = map proj_left l /\ lv = map proj_right l /\
        andl (map wf  l) /\ List.length l <= max_arity
    | cbv_split l ((cbv_update _ _ _ C' (fapply f lv) C'' v) as p) C (fapply f' lt) C''' v' =>
        C''' = C'' /\
        cache_path C C' l = true /\
        lt = map proj_left l /\ lv = map (@term_from_value _ _ _) (map proj_right l) /\
        andl (map wf  l) /\
        f = f' /\ v = v' /\
        wf  p /\ length l <= max_arity
    | cbv_split l ((cbv_read C' (fapply f lv) v) as p) C (fapply f' lt) C'' v' =>
        C'' = C' /\
        cache_path C C' l = true /\
        lt = map proj_left l /\ lv = map (@term_from_value _ _ _) (map proj_right l) /\
        andl (map wf  l) /\
        f = f' /\ v = v' /\
        wf  p /\ length l <= max_arity
    | cbv_update i s p C (fapply f lv as t0) C' v =>
        assoc term_beq t0 C = None /\
        exists lp t,
        i < length prog /\
        nth i prog rule_default = rule_intro f lp t /\
        lv = map (@term_from_value _ _ _) (map (psubst s) lp) /\
        proj_left p = subst s t /\ proj_right p = v /\
        cache_left p = C /\  True /\
        C' = (t0, v) :: cache_right p /\
        wf  p /\ length lv <= max_arity
    | cbv_read C (fapply _ lv as t) v =>
        assoc term_beq t C = Some v /\
        exists lv', lv = map (@term_from_value _ _ _) lv'
    | _ => False
  end.

Lemma wf_cbv_update i s p c1 t c2 v : wf (cbv_update i s p c1 t c2 v) -> wf p.
Proof.
destruct t; simpl; try tauto.
intro H; decompose record H; auto.
Qed.

Lemma wf_InCBV_wf p π: wf π -> InCBV p π -> wf p.
Proof.
intro H_π_wf.
apply cbv_reverse_induction.

- apply H_π_wf.

- intros lp c1 t c2 v _.
  simpl.
  destruct t; try (intro H_false; destruct H_false).
  destruct v.
  intros [ _ [ _ [ _ H_map_wf ] ] ] p' H_in_p'_lp.
  apply andl_in with (map wf lp).

  + apply H_map_wf.

  + apply in_map.
    apply H_in_p'_lp.

- intros lp p' c1 t c2 v H1 H2 p'' H3.
  simpl in H2.
  destruct p' as [ | | i s p' c1' t' c2' v' | c t' v' ]; try tauto.

  + destruct t' as [ | | f lv ]; try tauto.
    destruct t as [ | | f' lt ]; try tauto.
    destruct H2 as (H2 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & _).
    subst c2' lt lv f' v'.
    destruct H3 as [ H3 | H3 ]; try congruence.
    simpl in H10.
    destruct H10 as (H2 & lp' & t & H5 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15).
    subst v c1' c2.
    eapply andl_in.
    eexact H7.
    rewrite in_map_iff.
    eauto.

  + destruct t' as [ | | f lv ]; try tauto.
    destruct t as [ | | f' lt ]; try tauto.
    destruct H2 as (H2 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & _).
    subst c2 lt lv f' v'.
    destruct H3 as [ H3 | H3 ].

    * subst p''.
      trivial.

    * eapply andl_in.
      eexact H7.
      rewrite in_map_iff.
      eauto.

- intros i s p' c1 t c2 v H1 H2.
  simpl in H2.
  destruct t as [ | | f lv ]; try tauto.
  decompose record H2; assumption.
Qed.

(** ** Sizes *)
Definition cache_size (c : cache) : nat :=
  suml (map (fun tv => ╎ fst tv ╎ + value_size (snd tv)) c).

Fixpoint size_rec (π : cbv) : nat :=
  match π with
  | cbv_constr l c1 t c2 v => ╎t╎ + value_size v + suml (map size_rec l)
  | cbv_split l p c1 t c2 v => ╎t╎ + value_size v + size_rec p + suml (map size_rec l)
  | cbv_update _ _ p c1 t c2 v => size_rec p + ╎t╎ + value_size v
  | cbv_read c t v => ╎t╎ + value_size v
  end.

(** Size of a proof *)
Definition size (π : cbv) : nat :=
  size_rec π + cache_size (cache_left π).
Notation "'∣' p '∣'" := (size p) (at level 10).

(** Maximum size of an active judgement (𝓢) *)
Fixpoint 𝓢 (π : cbv) : nat :=
  match π with
  | cbv_constr lp _ _ _ _ => maxl (map 𝓢 lp)
  | cbv_split lp p _ _ _ _ => max (𝓢 p) (maxl (map 𝓢 lp))
  | cbv_update _ _ p _ t _ v => max (╎t╎ + value_size v) (𝓢 p)
  | cbv_read c t v => 0
  end.

Fixpoint max_judgement_size (π : cbv) : nat :=
  match π with
  | cbv_constr lp c1 t c2 v => max (╎t╎ + value_size v) (maxl (map max_judgement_size lp))
  | cbv_split lp p c1 t c2 v => max (╎t╎ + value_size v) (max (max_judgement_size p) (maxl (map max_judgement_size lp)))
  | cbv_update _ _ p c1 t c2 v => max (╎t╎ + value_size v) (max_judgement_size p)
  | cbv_read c t v => ╎t╎ + value_size v
  end.

(** Set of judgements (subtrees) *)

Fixpoint ℐ (π : cbv) : list cbv :=
  π :: (
    match π with
    | cbv_constr lp _ _ _ _ => flat_map ℐ lp
    | cbv_split lp p _ _ _ _ => flat_map ℐ (p :: lp)
    | cbv_update _ _ p _ _ _ _ => ℐ p
    | cbv_read _ _ _ => []
    end ).

Lemma ℐ_neq_nil : forall p, ℐ p <> [].
Proof.
destruct p; simpl; congruence.
Qed.

Lemma InCBV_In_ℐ p p' : InCBV p p' <-> In p (ℐ p').
Proof.
split.

- induction p' as [ lp c1 t c2 v IH_lp | lp p' c1 t c2 v IH_lp IH_p | i s p' c1 t c2 v IH_p | c t v ] using cbv_ind2; simpl.

  + intros [H1 | H1].

    * left.
      congruence.

    * right.
      rewrite in_flat_map.
      rewrite orl_map in H1.
      decompose record H1; eauto.

  + intros [H1 | [ H1 | H1 ] ].

    * left.
      congruence.

    * right.
      rewrite in_app_iff.
      left.
      apply IH_p.
      exact H1.

    * right.
      rewrite in_app_iff.
      right.
      rewrite in_flat_map.
      rewrite orl_map in H1.
      destruct H1 as (x & Hx1 & Hx2); eauto.

  + intros [H1 | H1].

    * left.
      congruence.

    * right.
      apply IH_p.
      exact H1.

  + intros [ H | H ]; try tauto.
    left.
    congruence.

- induction p' as [ lp c1 t c2 v IH_lp | lp p' c1 t c2 v IH_lp IH_p | i s p' c1 t c2 v IH_p | c t v ] using cbv_ind2;
  simpl; (intros [H1 | H1]; [left; congruence | right] ).

  + rewrite orl_map.
    rewrite in_flat_map in H1.
    decompose record H1; eauto.

  + rewrite in_app_iff in H1.
    destruct H1 as [H1 | H1]; [left; tauto | right].
    rewrite orl_map.
    rewrite in_flat_map in H1.
    decompose record H1; eauto.

  + tauto.

  + trivial.
Qed.

Lemma ℐ_size_rec_le p π :
  In p (ℐ π) -> size_rec p <= size_rec π.
Proof.
induction π as [ lp c1 t c2 v IH_lp | lp p' c1 t c2 v IH_lp IH_p | i s p' c1 t c2 v IH_p | c t v ] using cbv_ind2;
 unfold size; simpl; intros [ H1 | H1 ]; subst; trivial; try tauto.

- rewrite in_flat_map in H1.
  destruct H1 as (p' & H1 & H2).
  etransitivity.

  + apply IH_lp; eassumption.

  + clear IH_lp.
    rewrite plus_comm.
    apply le_plus_trans.
    apply in_le_suml.
    rewrite in_map_iff.
    eauto.

- rewrite in_app_iff, in_flat_map in H1.
  destruct H1 as [H1 | (p'' & H1 & H2) ].

  + clear IH_lp.
    etransitivity.

    * apply IH_p; trivial.

    * clear IH_p.
      omega.

  + clear IH_p.
    etransitivity.

    * apply IH_lp; eassumption.

    * clear IH_lp.
      rewrite plus_comm.
      apply le_plus_trans.
      apply in_le_suml.
      rewrite in_map_iff.
      eauto.

- apply IH_p in H1.
  omega.
Qed.

(* Return the proof tree of the list with the largest proj_left *)
Fixpoint proj_left_max_size_list (default : cbv) (proof_trees : list cbv) : cbv :=
  match proof_trees with
    | [] => default
    | [p] => p
    | p :: ps =>
      let p' := proj_left_max_size_list default ps in
      if leb (╎proj_left p╎) (╎proj_left p'╎) then p' else p
  end.

Lemma In_proj_left_max_size_list p lp : lp <> [] -> In (proj_left_max_size_list p lp) lp.
Proof.
induction lp as [ | p1 [ | p2 lp] IH]; simpl; try tauto.
intros _.
match goal with |- context [leb ?x ?y] => case_eq (leb x y); intro H_leb end.

- auto with *.

- tauto.
Qed.

Lemma proj_left_size_le_max_gen default proof_trees π:
  In π proof_trees ->
  ╎proj_left π╎ <= ╎proj_left (proj_left_max_size_list default proof_trees)╎.
Proof.
induction proof_trees as [ | p1 [ | p2 proof_trees ] IH]; simpl.

- tauto.

- intros [H1 | H1].

  + subst.
    trivial.

  + tauto.

- intros [H1 | [H1 | H1] ].

  + subst.
    match goal with |- context [leb ?x ?y] => case_eq (leb x y); intro H_leb end.

    * rewrite leb_iff in H_leb.
      exact H_leb.

    * trivial.

  + subst.
    match goal with |- context [leb ?x ?y] => case_eq (leb x y); intro H_leb end.

    * apply IH.
      simpl; tauto.

    * rewrite leb_iff_conv in H_leb.
      unfold lt in H_leb.
      { etransitivity.

        - apply IH.
          simpl; tauto.

        - simpl. omega.

      }

  + match goal with |- context [leb ?x ?y] => case_eq (leb x y); intro H_leb end.

    * apply IH.
      simpl; tauto.

    * { etransitivity.

        - apply IH.
          simpl; tauto.

        - rewrite leb_iff_conv in H_leb.
          simpl; omega.
      }
Qed.

Definition proj_left_max_size (π : cbv) : cbv :=
  proj_left_max_size_list π (ℐ π).

Lemma proj_left_size_le_max π:
  forall p, InCBV p π ->
  ╎proj_left p╎ <= ╎proj_left (proj_left_max_size π)╎.
Proof.
intros p H_InCBV.
apply proj_left_size_le_max_gen.
apply InCBV_In_ℐ.
trivial.
Qed.

Lemma InCBV_proj_left_max_size p : InCBV (proj_left_max_size p) p.
Proof.
unfold proj_left_max_size.
apply InCBV_In_ℐ.
apply In_proj_left_max_size_list.
apply ℐ_neq_nil.
Qed.

Fixpoint max_proj_right_size (π : cbv) : nat :=
  match π with
  | cbv_constr lp _ t _ v => max (value_size v) (maxl (map max_proj_right_size lp))
  | cbv_split lp p _ t _ v => max (value_size v) (max (max_proj_right_size p) (maxl (map max_proj_right_size lp)))
  | cbv_update _ _ p _ t _ v => max (value_size v) (max_proj_right_size p)
  | cbv_read _ t v => value_size v
  end.

Lemma judgement_size_le_projs_size p :
  max_judgement_size p <= ╎proj_left (proj_left_max_size p)╎ + max_proj_right_size p.
Proof.
induction p as [ lp c1 t c2 v IH_lp | lp p c1 t c2 v IH_lp IH_p | i s p c1 t c2 v IH_p | c t v ] using cbv_ind2; simpl.

- destruct (max_dec (╎t╎ + value_size v) (maxl (map max_judgement_size lp))) as [ H | H ];
  rewrite H.

  + apply plus_le_compat.

    * change t with (proj_left (cbv_constr lp c1 t c2 v)) at 1.
      apply proj_left_size_le_max.
      apply InCBV_refl.

    * apply le_max_l.

  + apply maxl_le_maxl in IH_lp.
    etransitivity.

    * apply IH_lp.

    * { etransitivity.

      - apply maxl_map_plus_le.

      - apply plus_le_compat.

        + apply all_max_le.
          intros size H1.
          rewrite in_map_iff in H1.
          destruct H1 as (p & H1 & H2).
          subst size.
          apply proj_left_size_le_max.
          eapply InCBV_trans.
          apply InCBV_proj_left_max_size.
          apply InCBV_In_ℐ.
          simpl.
          right.
          rewrite in_flat_map.
          exists p.
          split; trivial.
          apply InCBV_In_ℐ.
          apply InCBV_refl.

        + apply le_max_r.

      }

- destruct (max_dec (╎t╎ + value_size v) (max (max_judgement_size p) (maxl (map max_judgement_size lp)))) as [ H1 | H1 ];
  rewrite H1.

  + apply plus_le_compat.

    * change t with (proj_left ((cbv_split lp p c1 t c2 v))) at 1.
      apply proj_left_size_le_max.
      apply InCBV_refl.

    * apply le_max_l.

  + destruct (max_dec (max_judgement_size p) (maxl (map max_judgement_size lp))) as [ H2 | H2 ];
    rewrite H2.

    * { etransitivity.

        - apply IH_p.

        - apply plus_le_compat.

          + apply proj_left_size_le_max.
            simpl.
            right.
            left.
            apply InCBV_proj_left_max_size.

          + etransitivity; [idtac | apply le_max_r]; apply le_max_l.

      }

    * { apply maxl_le_maxl in IH_lp.
        etransitivity.

        - apply IH_lp.

        - etransitivity.

          + apply maxl_map_plus_le.

          + apply plus_le_compat.

            * apply all_max_le.
              intros size H3.
              rewrite in_map_iff in H3.
              destruct H3 as (p' & H3 & H4).
              subst size.
              apply proj_left_size_le_max.
              eapply InCBV_trans.
              apply InCBV_proj_left_max_size.
              apply InCBV_In_ℐ.
              simpl.
              right.
              rewrite in_app_iff.
              right.
              rewrite in_flat_map.
              exists p'.
              split; trivial.
              apply InCBV_In_ℐ.
              apply InCBV_refl.

            * etransitivity; [idtac | apply le_max_r]; apply le_max_r.

      }

- destruct (max_dec (╎t╎ + value_size v) (max_judgement_size p)) as [ H | H ];
  rewrite H.

  + apply plus_le_compat.

    * change t with (proj_left ((cbv_update i s p c1 t c2 v))) at 1.
      apply proj_left_size_le_max.
      apply InCBV_refl.

    * apply le_max_l.

  + etransitivity.

    * apply IH_p.

    * { apply plus_le_compat.

        - apply proj_left_size_le_max.
          simpl.
          right.
          apply InCBV_proj_left_max_size.

        - apply le_max_r.
      }

- trivial.
Qed.

(** ** Activations (ℐᵃ) *)
Fixpoint ℐᵃ (π : cbv) : list cbv :=
  match π with
  | cbv_constr lp _ _ _ _ => flat_map ℐᵃ lp
  | cbv_split lp p _ _ _ _ => ℐᵃ p ++ flat_map ℐᵃ lp
  | cbv_update _ _ p _ _ _ _ as p' => p' :: ℐᵃ p
  | cbv_read _ _ _ => []
  end.

Definition 𝓐 (π : cbv) := length (ℐᵃ π).
Arguments 𝓐 / π.

Fixpoint ℐᵃ_cache_order (π : cbv) : list cbv :=
  match π with
  | cbv_constr lp _ _ _ _ => revflatten (map ℐᵃ_cache_order lp)
  | cbv_split lp p _ _ _ _ => ℐᵃ_cache_order p ++ revflatten (map ℐᵃ_cache_order lp)
  | cbv_update _ _ p _ _ _ _ as p' => p' :: ℐᵃ_cache_order p
  | cbv_read _ _ _ => []
  end.

Lemma ℐᵃ_cache_order_are_ℐᵃ (p: cbv) :
  Permutation (ℐᵃ p) (ℐᵃ_cache_order p).
Proof.
  induction p using cbv_ind2.
  - simpl.
    induction lp.
    + apply Permutation_refl.

    + simpl.
      rewrite Permutation_app_comm.
      apply Permutation_app; auto with *.

  - simpl.
    apply Permutation_app.
    + assumption.

    + apply Permutation_sym; eapply Permutation_trans.
      * apply Permutation_revflatten.

      * apply Permutation_flat_map_ext.
        intros x Hx; apply Permutation_sym.
        apply H; assumption.

  - simpl. apply perm_skip; assumption.

  - apply Permutation_refl.
Qed.

Lemma ℐᵃ_are_subtrees: forall p pi:cbv,
   In p (ℐᵃ pi) -> In p (ℐ pi).
Proof.
intros.
induction pi using cbv_ind2;simpl;simpl in H.
(* cbv_read: no ℐᵃ *)
 4: exfalso;auto.
(* cbv_update *)
 3: elim H;intros.
 3: left;auto.
 3: right.
 3: apply IHpi;auto.
(* cbv_constr *)
 right.
 induction lp;simpl;simpl in H;auto.
 (*  cons *)
  apply in_or_app.
  apply in_app_or in H.
  elim H;intros.
  (* head *)
   left;apply H0;simpl;auto.
  (* tail: induction *)
   right.
   apply IHlp;auto.
   intros.
   apply H0;auto.
   simpl;auto.
(* cbv_split *)
 right.
 apply in_or_app.
 apply in_app_or in H.
 elim H;intros.
 left;apply IHpi;auto.
 right.
 induction lp;simpl;simpl in H1;auto.
 (* cons *)
  apply in_or_app.
  apply in_app_or in H1.
  elim H1;intros.
  (* head *)
   left;apply H0;simpl;auto.
  (* tail: induction *)
   right.
   apply IHlp;auto.
   intros.
   apply H0;auto.
   simpl;auto.
Qed.

Corollary ℐᵃ_inCBV: forall p pi:cbv,
   In p (ℐᵃ pi) -> InCBV p pi.
Proof.
intros.
apply InCBV_In_ℐ.
apply ℐᵃ_are_subtrees;auto.
Qed.

Definition functions_of_prog : list function :=
  map (fun x => match x with | rule_intro f _ _ => f end) prog.

Lemma activation_is_function :
  forall π p,
  In p (ℐᵃ π) -> exists i s p' c1 t c2 v, p = cbv_update i s p' c1 t c2 v.
Proof.
intros π p H.
induction π as [ lp c1 t c2 v IH | lp p' c1 t c2 v IH_lp IH_p' | i s p' c1 t c2 v IH | c t v ] using cbv_ind2.

- (* cbv_constr *)
  simpl in H.
  apply in_flat_map in H.
  destruct H as [ x H ].
  destruct H as [ H_x_in H_p_in_x ].
  generalize (IH x H_x_in H_p_in_x).
  trivial.

- (* cbv_split *)
  simpl in H.
  apply in_app_or in H.
  destruct H as [ H_p' | H_lp ].

  + refine (IH_p' H_p').

  + apply in_flat_map in H_lp.
    destruct H_lp as [ x H ].
    destruct H as [ H_x_in H_p_in_x ].
    generalize (IH_lp x H_x_in H_p_in_x).
    trivial.

- (* cbv_update *)
  simpl in H.
  destruct H as [ H_base | H_ind ].

  + repeat eexists.
    symmetry.
    apply H_base.

  + generalize (IH H_ind).
    trivial.

- simpl in H; tauto.
Qed.


Lemma cbv_update_in_ℐᵃ_InCBV π sub_proof_tree i s p c1 t c2 v:
  sub_proof_tree = cbv_update i s p c1 t c2 v ->
  InCBV sub_proof_tree π ->
  In sub_proof_tree (ℐᵃ π).
Proof.
intros H0 H1.
subst.
induction π as [ lp c1' t' c2' v' IH | lp p' c1' t' c2' v' IH1 IH2 | i' s' p' c1' t' c2' v' IH | c t' v' ] using cbv_ind2; simpl in *.

- destruct H1 as [H1 | H1]; try discriminate H1.
  rewrite in_flat_map.
  rewrite orl_map in H1.
  decompose record H1; eauto.

- destruct H1 as [H1 | [H1 | H1] ]; try discriminate.

  + apply in_or_app.
    tauto.

  + rewrite in_app_iff, in_flat_map.
    rewrite orl_map in H1.
    destruct H1 as (p'' & H1 & H2).
    right.
    exists p''.
    eauto.

- destruct H1 as [ H1 | H1 ]; try tauto.
  left.
  congruence.

- destruct H1 as [H1 | H1].

  + congruence.

  + trivial.
Qed.

Lemma ℐᵃ_wf : forall π p, wf π -> In p (ℐᵃ π) -> wf p.
Proof.
intros π p H1; revert p; induction π as [ lp c1 t c2 v IH | lp p' c1 t c2 v IH1 IH2 | i s p' c1 t c2 v IH | c t v ] using cbv_ind2;
intros p H2; simpl in * |-.

- destruct t as [ x | c lt | f lt ]; try tauto.
  destruct v as [ c' lv ].
  destruct H1 as (H1 & H3 & H4 & H5 & H6 & _).
  subst c' lt lv.
  rewrite in_flat_map in H2.
  destruct H2 as (p' & H2 & H3).
  apply IH with p'; trivial.
  apply andl_in with (P := wf p') in H6; trivial.
  apply in_map_iff.
  eauto.

- destruct p' as [ | | i s p' c1' t' c2' v' | c t' v' ]; try tauto.

  + destruct t' as [ | | f lv ]; try tauto.
    destruct t as [ | | f' lt ]; try tauto.
    destruct H1 as (H1 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & _).
    subst c2' lt lv f' v'.
    rewrite in_app_iff in H2.
    destruct H2 as [ H2 | H2 ]; auto.
    rewrite in_flat_map in H2.
    destruct H2 as (p'' & H1 & H4).
    apply (IH1 _ H1); trivial.
    eapply andl_in.
    eexact H6.
    rewrite in_map_iff.
    exists p''; split; auto.

  + destruct t' as [ | | f lv ]; try tauto.
    destruct t as [ | | f' lt ]; try tauto.
    destruct H1 as (H1 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & _).
    subst c2 lt lv f' v'.
    rewrite in_app_iff in H2.
    destruct H2 as [ H2 | H2 ]; auto.
    rewrite in_flat_map in H2.
    destruct H2 as (p'' & H1 & H4).
    apply (IH1 _ H1); trivial.
    eapply andl_in.
    eexact H6.
    rewrite in_map_iff.
    exists p''; split; auto.

- destruct t as [ | | f lv ]; try tauto.
  destruct H1 as (H1 & lp & t & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12).
  destruct H2 as [ H2 | H2 ]; auto.
  subst lv v c1 c2 p.
  split.
  + auto.

  + exists lp; exists t; repeat split; auto.

- tauto.
Qed.

Lemma le_𝓢 π p :
  In p (ℐᵃ π) ->
  ╎proj_left p╎ + value_size (proj_right p) <= 𝓢 π.
Proof.
intro H.
induction π as [ lp c1 t c2 v IH | lp p' c1 t c2 v IH_lp IH_p' | i s p' c1 t c2 v IH | c t v ] using cbv_ind2; simpl in *.

- rewrite in_flat_map in H.
  destruct H as (p' & H1 & H2).

  + etransitivity.

    * apply IH.
      eexact H1.
      tauto.

    * apply maxl_is_max.
      rewrite in_map_iff.
      exists p'; split; trivial.

- rewrite in_app_iff in H.
  destruct H as  [ H | H ].

  + etransitivity.

    * apply IH_p'.
      tauto.

    * apply le_max_l.

  + rewrite in_flat_map in H.
    destruct H as (p'' & H1 & H2).
    etransitivity.

    * apply IH_lp.
      eexact H1.
      tauto.

    * etransitivity; [idtac | apply le_max_r].
      apply maxl_is_max.
      apply in_map_iff.
      exists p''.
      tauto.

- destruct H as [ H | H ].

  + subst p.
    simpl in *.
    etransitivity; [idtac | apply le_max_l].
    trivial.

  + etransitivity; [idtac | apply le_max_r].
    apply IH.
    tauto.

- tauto.
Qed.

Hypothesis prog_is_wf : wf_prog max_arity prog.

Lemma 𝓡_spec ( subst_default : variable -> value) :
  forall π, wf π -> forall p, In p (ℐᵃ π) ->
  let (i, s) := rule_subst_of_cbv_update subst_default p in
  ╎subst s (rhs_of_rule (nth i prog rule_default))╎ <= 𝓡 prog (╎proj_left p╎).
Proof.
intros π H_wf_π p H_p_activation.
case_eq (rule_subst_of_cbv_update subst_default p).
intros i s H_p_fun.
unfold 𝓡.
set (rule_i := nth i prog rule_default);
set (l := lhs_of_rule rule_i);
set (r := rhs_of_rule rule_i);
set (t := proj_left p).
rewrite step_one.
apply mult_le_compat.

- apply maxl_is_max; rewrite map_map, in_map_iff; exists rule_i; split.

  + reflexivity.

  + apply nth_In.
    generalize (ℐᵃ_wf H_wf_π H_p_activation); intro H_wf_p.
    generalize (activation_is_function H_p_activation); intros (i' & s' & p' & c1 & t' & c2 & v & H_p_is_function).
    subst p.
    simpl in H_p_fun.
    injection H_p_fun; clear H_p_fun; intros; subst i' s'.
    simpl in H_wf_p.
    destruct t'; try tauto.
    destruct H_wf_p as (_ & lp & t' & H); tauto.

- apply plus_le_compat_l.
  transitivity (max_size_image_subst l s).

  + (* variables in r must appear on the left-hand-side *)
    apply incl_le_max_size_image_subst.
    assert (rule_vars_defined rule_i) as H_wf_rule_i.
    * { eapply andl_in.

      - destruct prog_is_wf as [ Hwfrule _ ].
        exact Hwfrule.

      - rewrite in_map_iff.
        exists rule_i.
        split; trivial.
        apply nth_In.
        generalize (ℐᵃ_wf H_wf_π H_p_activation); intro H_wf_p.
        generalize (activation_is_function H_p_activation); intros (i' & s' & p' & c1 & t' & c2 & v & H_p_is_function).
        subst p.
        simpl in H_p_fun.
        injection H_p_fun; clear H_p_fun; intros; subst i' s'.
        simpl in H_wf_p.
        destruct t'; try tauto.
        destruct H_wf_p as (_ & lp & t' & H); tauto. }

    * { destruct rule_i as [f lp t'].
        simpl in H_wf_rule_i.
        unfold l, r.
        simpl.
        replace (flat_map (@vars_of_term _ _ _) (map (@term_from_pattern _ _ _) lp)) with (flat_map (@vars_of_pattern _ _) lp).

          - exact H_wf_rule_i.

          - apply flat_map_comp; intros; apply vars_of_pattern_term. }

  + assert (subst s l = t) as H_t_matches_lhs.

    * generalize (ℐᵃ_wf H_wf_π H_p_activation); intro H_wf_p.
      generalize (activation_is_function H_p_activation); intros (i' & s' & p' & c1 & t' & c2 & v & H_p_is_function).
      unfold t; clear t.
      subst p.
      simpl.
      simpl in H_p_fun.
      injection H_p_fun; clear H_p_fun; intros; subst i' s'.
      simpl in H_wf_p.
      destruct t' as [ | | f lt]; try tauto.
      destruct H_wf_p as (_ & lp & t' & H1 & H2 & H3 & H4 & H5 & H6).
      unfold l, r, rule_i in *; clear l r rule_i.
      rewrite H2.
      subst lt v.
      simpl.
      f_equal.
      do 2 rewrite map_map.
      clear.
      induction lp as [ | p lp IH]; simpl; trivial.
      rewrite IH.
      f_equal.
      apply subst_psubst.

    * replace t with (subst s l).
      apply max_size_image_subst_bounded.
Qed.

(** Number of judgments *)
Fixpoint nb_judgements (π : cbv) : nat :=
  match π with
  | cbv_constr lp _ _ _ _ => 1 + suml (map nb_judgements lp)
  | cbv_split lp p _ _ _ _ => 1 + nb_judgements p + suml (map nb_judgements lp)
  | cbv_update _ _ p _ _ _ _ => 1 + nb_judgements p
  | cbv_read _ _ _=> 1
  end.
Notation "#ℐ" := nb_judgements.

(** Number of pseudo-dependencies *)
Fixpoint nb_judgements_sub_rec (π : cbv) : nat :=
  match π with
  | cbv_constr lp _ _ _ _ => 1 + suml (map nb_judgements_sub_rec lp)
  | cbv_split lp p _ _ _ _ => 1 + nb_judgements_sub_rec p + suml (map nb_judgements_sub_rec lp)
  | cbv_update _ _ _ _ _ _ _ => 0
  | cbv_read _ _ _ => 0
  end.
Notation "#𝓓'" := nb_judgements_sub_rec.

(** Number of dependencies *)

Definition nb_judgements_sub (π : cbv) : nat :=
  match π with
  | cbv_constr _ _ _ _ _ => 0
  | cbv_split _ _ _ _ _ _ => 0
  | cbv_update _ _ p _ _ _ _ => #𝓓' p
 | cbv_read _ _ _ => 0
  end.
Notation "#𝓓" := nb_judgements_sub.

(** Number of active and passive nodes *)
Fixpoint nb_nodes (π : cbv) : nat :=
  match π with
  | cbv_constr [] _ _ _ _ => 0
  | cbv_constr lp _ _ _ _ => 1 + suml (map nb_nodes lp)
  | cbv_split lp p _ _ _ _ => 1 + nb_nodes p + suml (map nb_nodes lp)
  | cbv_update _ _ p _ _ _ _ => 1 + nb_nodes p
  | cbv_read _ _ _ => 0
  end.
Notation "#ℐᵃ⁺ᵖ" := nb_nodes.


(** number of semi-active judgements *)
Fixpoint nb_read (π : cbv) : nat :=
  match π with
  | cbv_constr lp _ _ _ _ => suml (map nb_read lp)
  | cbv_split lp p _ _ _ _ => nb_read p + suml (map nb_read lp)
  | cbv_update _ _ p _ _ _ _ => nb_read p
  | cbv_read _ _ _ => 1
  end.
Notation "#ℐˢ" := nb_read.

Definition arity_cbv (π : cbv) : nat :=
  match π with
  | cbv_constr lp _ _ _ _  => length lp
  | cbv_split lp p _ _ _ _ => 1 + length lp
  | cbv_update _ _ p _ _ _ _ => 1
  | cbv_read _ _ _ => 0
  end.

Lemma wf_arity p : wf p -> arity_cbv p <= S max_arity.
Proof.
intro H_wf_p.
induction p as [ lp c1 t c2 v IH_lp | lp p c1 t c2 v IH_lp IH_p | i s p c1 t c2 v IH_p | c t v ] using cbv_ind2;
 simpl; try omega; simpl in * |-.

- destruct t as [ | c lt | ]; try tauto.
  destruct v as [ c' lv ].
  omega.

- destruct p as [ | | i s p c1' t' c2' v' | c t' v' ]; try tauto.

  + destruct t' as [ | | f lv ]; try tauto.
    destruct t as [ | | f' lt ]; try tauto.
    omega.

  + destruct t' as [ | | f lv ]; try tauto.
    destruct t as [ | | f' lt ]; try tauto.
    omega.
Qed.

(** ** Bounding semi-active judgements *)

(** Proposition 24 *)
Lemma nb_read_bound : forall p,
   wf p ->
  #ℐˢ p <= S (max_arity * #ℐᵃ⁺ᵖ p).
Proof.
intros p H_wf_p.
induction p as [ lp c1 t c2 v IH_lp | lp p c1 t c2 v IH_lp IH_p | i s p c1 t c2 v IH_p | c t v ] using cbv_ind2.

- simpl nb_read.
  etransitivity.

  + apply suml_map_le.
    intros p Hp.
    apply IH_lp; clear IH_lp; trivial.
    eapply wf_InCBV_wf.

    * eexact H_wf_p.

    * simpl.
      right.
      rewrite orl_map.
      eexists p.
      split; trivial.
      apply InCBV_refl.

  + clear IH_lp.
    destruct lp as [ | p lp]; simpl nb_nodes.

    * simpl; omega.

    * rewrite map_cons, suml_cons.
      rewrite mult_succ_r, mult_plus_distr_l, <- plus_assoc, <- plus_Sn_m.
      apply plus_le_compat_l.
      rewrite mult_suml_r.
      rewrite map_map.
      change (S ?x) with (1 + x).
      rewrite suml_map_plus.
      rewrite plus_comm.
      apply plus_le_compat_l.
      rewrite suml_map_const.
      rewrite mult_1_l.
      apply wf_arity in H_wf_p.
      simpl in H_wf_p.
      omega.

- simpl nb_read.
  etransitivity.

  + apply plus_le_compat.

    * apply IH_p.
      {eapply wf_InCBV_wf.

        - eexact H_wf_p.

        - simpl.
          right; left.
          apply InCBV_refl.
      }

    * clear IH_p.
      apply suml_map_le.
      intros p' Hp'.
      apply IH_lp; trivial.
      {eapply wf_InCBV_wf.

        - eexact H_wf_p.

        - simpl.
          right; right.
          rewrite orl_map.
          eexists p'.
          split; trivial.
          apply InCBV_refl.
      }

  + clear IH_p IH_lp.
    destruct lp as [ | p' lp]; simpl nb_nodes.

    * simpl. ring_simplify; omega.

    * rewrite map_cons, suml_cons.
      rewrite mult_succ_r, mult_plus_distr_l, <- plus_assoc, <- plus_Sn_m.
      apply plus_le_compat_l.
      rewrite mult_plus_distr_l, plus_Snm_nSm, <- plus_assoc.
      apply plus_le_compat_l.
      rewrite mult_suml_r.
      rewrite map_map.
      change (S (?x * ?y)) with (1 + x * y).
      rewrite suml_map_plus.
      rewrite plus_comm.
      rewrite plus_n_Sm.
      apply plus_le_compat_l.
      rewrite suml_map_const.
      rewrite mult_1_l.
      apply wf_arity in H_wf_p.
      simpl in H_wf_p.
      omega.

- simpl nb_read.
  simpl nb_nodes.
  etransitivity.

  + apply IH_p.
    apply wf_cbv_update in H_wf_p.
    exact H_wf_p.

  + ring_simplify; omega.

- simpl; omega.
Qed.

(** ** First activations *)
Fixpoint first_activations_rec (π : cbv) : list cbv :=
  match π with
  | cbv_constr lp _ _ _ _ => flat_map first_activations_rec lp
  | cbv_split lp p _ _ _ _ => first_activations_rec p ++ flat_map first_activations_rec lp
  | cbv_update _ _ _ _ _ _ _ as p' => [p']
  | cbv_read _ _ _ => []
  end.

Definition first_activations (π : cbv) : list cbv :=
  match π with
  | cbv_constr lp _ _ _ _ => []
  | cbv_split lp p _ _ _ _ => []
  | cbv_update _ _ p _ _ _ _ => first_activations_rec p
  | cbv_read _ _ _ => []
  end.

Definition strict_activations (π: cbv) :=
  flat_map ℐᵃ (first_activations π).

Lemma first_activation_rec_is_update π p :
  In p (first_activations_rec π) -> exists i s p' c1 t c2 v, p = cbv_update i s p' c1 t c2 v.
Proof.
intros H.
induction π as [ lp c1 t c2 v IH | lp p' c1 t c2 v IH_lp IH_p' | i s p' c1 t c2 v IH | c t v ] using cbv_ind2;
 simpl in H.

- rewrite in_flat_map in H.
  decompose record H; eauto.

- rewrite in_app_iff, in_flat_map in H.
  decompose [or ex and] H; eauto.

- destruct H as [ H | H ]; try tauto.
  subst p.
  repeat eexists.

- tauto.
Qed.

Lemma first_activation_is_update π p :
  In p (first_activations π) -> exists i s p' c1 t c2 v, p = cbv_update i s p' c1 t c2 v.
Proof.
intros H.
destruct π as [ lp c1 t c2 v | lp p' c1 t c2 v | i s p' c1 t c2 v | c t v ]; simpl in H; try tauto.
apply first_activation_rec_is_update with p'.
exact H.
Qed.

Lemma in_first_activations_rec_nb_judgements_le p π :
  In p (first_activations_rec π) -> #ℐ p <= #ℐ π.
Proof.
induction π as [lp c1 t c2 v IH_lp | lp p' c1 t c2 v IH_lp IH_p' | i s p' c1 t c2 v IH_p' | c t v] using cbv_ind2; simpl; intros H1.

- rewrite in_flat_map in H1.
  destruct H1 as (p' & H1 & H2).
  etransitivity.

  + apply IH_lp; eassumption.

  + clear IH_lp.
    apply le_S.
    apply in_le_suml.
    rewrite in_map_iff.
    eauto.

- rewrite in_app_iff, in_flat_map in H1.
    destruct H1 as [ H1 | (p'' & H1 & H2) ].

  + apply le_S.
    apply le_plus_trans.
    apply IH_p'; trivial.

  + clear IH_p'.
    transitivity (#ℐ p'').
    apply IH_lp; trivial.
    apply le_S.
    rewrite plus_comm.
    apply le_plus_trans.
    apply in_le_suml.
    rewrite in_map_iff.
    eauto.

- destruct H1 as [ H1 | H1 ]; try tauto.
  subst p.
  trivial.

- tauto.
Qed.

Lemma in_first_activations_nb_judgements_lt p π :
  In p (first_activations π) -> #ℐ p < #ℐ π.
Proof.
intros H1.
destruct π as [ lp c1 t c2 v | lp p' c1 t c2 v | i s p' c1 t c2 v | c t v ]; simpl in H1; try tauto.
apply le_lt_trans with (#ℐ p').

- apply in_first_activations_rec_nb_judgements_le; trivial.

-
simpl; omega.
Qed.

Lemma first_activations_rec_incl_ℐᵃ (p: cbv) :
  incl (first_activations_rec p) (ℐᵃ p).
Proof.
unfold incl.
induction p as [lp c1 t c2 v IHlp | lp p' c1 t c2 v IHlp IHp' | i s p' c1 t c2 v IHp' | c t v] using cbv_ind2;
 trivial; simpl; try tauto.

- intros p Hp.
  rewrite in_flat_map in *.
  destruct Hp as (p' & Hp1 & Hp2).
  exists p'.
  auto.

- intros p Hp.
  rewrite in_app_iff, in_flat_map in *.
  destruct Hp as [ Hp | Hp ]; auto.
  right.
  destruct Hp as (p'' & Hp1 & Hp2).
  exists p''.
  auto.
Qed.

Lemma first_activations_incl_ℐᵃ (p: cbv) :
  incl (first_activations p) (ℐᵃ p).
Proof.
destruct p; try (unfold incl; simpl; tauto).
simpl.
apply incl_tl, first_activations_rec_incl_ℐᵃ.
Qed.

Fixpoint first_activations_and_semi_rec (π : cbv) : list cbv :=
  match π with
  | cbv_constr lp _ _ _ _          => flat_map first_activations_and_semi_rec lp
  | cbv_split lp p _ _ _ _         => first_activations_and_semi_rec p ++ flat_map first_activations_and_semi_rec lp
  | cbv_update _ _ _ _ _ _ _ as p' => [p']
  | cbv_read _ _ _ as p'           => [p']
  end.

Definition first_activations_and_semi (π : cbv) : list cbv :=
  match π with
  | cbv_constr lp _ _ _ _    => []
  | cbv_split lp p _ _ _ _   => []
  | cbv_update _ _ p _ _ _ _ => first_activations_and_semi_rec p
  | cbv_read _ _ _           => []
  end.

Lemma incl_first_activations_semi p :
  incl (first_activations p) (first_activations_and_semi p).
Proof.
unfold first_activations, first_activations_and_semi.
destruct p as [ | | _ _ p _ _ _ _ | ]; simpl; try congruence.
induction p as [ | | | ] using cbv_ind2; simpl; try congruence; auto with *.

- apply incl_flat_map; trivial.

- apply incl_app; auto with *.
  apply incl_appr, incl_flat_map; trivial.
Qed.

Lemma first_activations_and_semi_rec_incl_ℐ p :
  incl (first_activations_and_semi_rec p) (ℐ p).
Proof.
  induction p as [ lp c1 t c2 v IHlp | lp p' c1 t c2 v IHlp IHp' | i s p' c1 t c2 v IHp' | c t v ]
              using cbv_ind2;
  simpl.

  - (* cbv_constr *)
    apply incl_tl.
    revert IHlp; clear.
    induction lp as [ | p lp IH ]; intros IHlp; simpl; [ intros p Hin; assumption | idtac ].
    apply incl_app.
    + apply incl_tran with (m := ℐ p).
      * apply IHlp; simpl; tauto.
      * apply incl_appl; apply incl_refl.
    + apply incl_tran with (m := flat_map ℐ lp).
      * apply IH.
        intros; apply IHlp; simpl; tauto.
      * apply incl_appr; apply incl_refl.

  - (* cbv_split *)
    apply incl_tl.
    apply incl_app.
    + apply incl_appl; assumption.
    + apply incl_appr.
      revert IHlp; clear.
      induction lp as [ | p lp IH ]; intros IHlp; simpl; [ intros p Hin; assumption | idtac ].
      apply incl_app.
      * { apply incl_tran with (m := ℐ p).
          - apply IHlp; simpl; tauto.
          - apply incl_appl; apply incl_refl.
        }
      * { apply incl_tran with (m := flat_map ℐ lp).
          - apply IH.
            intros; apply IHlp; simpl; tauto.
          - apply incl_appr; apply incl_refl.
        }

  - (* cbv_update *)
    intros p Hin; simpl; left.
    simpl in Hin; destruct Hin as [ Heq | ]; tauto.

  - (* cbv_read *)
    apply incl_refl.
Qed.

Lemma first_activations_and_semi_incl_ℐ p :
  incl (first_activations_and_semi p) (ℐ p).
Proof.
  destruct p; try (unfold incl; simpl; intros; tauto).
  simpl.
  apply incl_tl; apply first_activations_and_semi_rec_incl_ℐ.
Qed.

(** Induction principle on proof trees based on first-ℐᵃ *)
Lemma cbv_big_induction :
  forall (P : cbv -> Prop),
  (forall i s p c1 t c2 v, (forall p', In p' (first_activations (cbv_update i s p c1 t c2 v)) -> P p') -> P (cbv_update i s p c1 t c2 v)) ->
  forall i s p c1 t c2 v, P (cbv_update i s p c1 t c2 v).
Proof.
intros P H1 i s p c1 t c2 v.
remember (#ℐ (cbv_update i s p c1 t c2 v)) as nbj eqn:Hsize.
revert i s p c1 t c2 v Hsize.
induction nbj as [ nbj' IH ] using lt_wf_ind.
intros i s p c1 t c2 v Hsize.
apply H1.
clear H1.
intros p'' H1.
generalize H1; intro H2.
apply first_activation_is_update in H2.
destruct H2 as (i' & s' & p' & c1' & t' & c2' & v' & H2).
subst p''.
apply IH with (m := #ℐ (cbv_update i' s' p' c1' t' c2' v')); trivial; clear IH.
subst nbj'.
apply in_first_activations_nb_judgements_lt.
exact H1.
Qed.

Lemma ℐᵃ_first_activations i s p' c1 t c2 v :
  let p := cbv_update i s p' c1 t c2 v in
  ℐᵃ p = p :: flat_map ℐᵃ (first_activations p).
Proof.
unfold first_activations.
simpl.
f_equal.
induction p' as [lp c1' t' c2' v' IH_lp | lp p c1' t' c2' v' IH_lp IH_p | i' s' p c1' t' c2' v' IH_p | c t' v'] using cbv_ind2;
 simpl; simpl_list; trivial.

- apply comp_flat_map in IH_lp.
  trivial.

- apply comp_flat_map in IH_lp.
  rewrite flat_map_app.
  congruence.
Qed.

(** ** Properties on caches *)

(** The initial cache of a well-formed term is a coherent prefix of the final cache *)
Lemma cache_consistent p :
  wf p ->
  exists C,
    cache_beq (cache_right p) (C ++ cache_left p) = true /\
    (forall t, assoc_cache t C <> None -> assoc_cache t (cache_left p) = None).
Proof.
induction p as [lp c1 t c2 v IHlp | lp p' c1 t c2 v IHlp IHp' | i s p' c1 t c2 v IHp' | c t v] using cbv_ind2;
intros Hwf.

- (* cbv_constr *)
  simpl in Hwf; destruct t as [ | c lt | ] in Hwf; try tauto.
  destruct v as [ c' lv ].
  destruct Hwf as ( Hcache & Heqc & Heqlt & Heqlv & Hwflp & _ ).
  subst c'.
  simpl.
  revert c1 c2 lt lv Heqlt Heqlv Hwflp Hcache.
  induction lp as [ | p' lp' IHlp' ]; intros c1 c2 lt lv Heqlt Heqlv Hwflp Hcache.

  + exists [].
    simpl in Hcache.
    simpl.
    split.

    * apply cache_beq_eq; trivial.
      apply cache_beq_eq in Hcache; trivial.
      auto.

    * tauto.

  + destruct (IHlp p') as (Cp' & HeqCp' & HassocCp').

    * simpl; tauto.

    * destruct Hwflp as [ Hwfp' _ ]; trivial.

    * { apply cache_beq_eq in HeqCp'; trivial.
        simpl in Hcache.
        rewrite Bool.andb_true_iff in Hcache.
        destruct Hcache as (Hcachec1 & Hcachepathlp').
        destruct IHlp' with (c1 := cache_right p')
                            (c2 := c2)
                            (lt:= map proj_left lp')
                            (lv:= map proj_right lp')
                       as (Clp' & HeqClp' & HassocClp');
        trivial.

      - intros p Hinp Hwfp.
        apply IHlp; trivial.
        simpl; tauto.

      - simpl in Hwflp. tauto.

      - apply cache_beq_eq in HeqClp'; trivial.
        exists (Clp' ++ Cp').
        apply cache_beq_eq in Hcachec1; trivial.
        subst c1.
        split.

        + apply cache_beq_eq; trivial.
          rewrite <- app_assoc.
          congruence.

        + intros t' Hassoct'.
          rewrite assoc_app_neq_None in Hassoct'.
          destruct Hassoct' as [ Hassoct' | Hassoct' ]; auto.
          generalize (HassocClp' t' Hassoct'); intros HrightNone.
          rewrite HeqCp' in HrightNone.
          rewrite assoc_app_eq_None in HrightNone.
          tauto. }

- (* cbv_split *)
  apply forall_exists_list in IHlp.

  + destruct IHlp as [ Clp HClp ].

    assert (wf p' /\
            andl (map wf lp) /\
            c2 = cache_right p' /\
            cache_path c1 (cache_left p') lp = true)
      as (Hwfp' & Hwflp & Heqc2 & Heqpath). {
      simpl in Hwf.
      destruct p'; try tauto; try (destruct t0; [ | destruct t | destruct t]; tauto).
      }

    destruct (IHp' Hwfp') as (Cp' & HeqCp' & HCp').
    apply cache_beq_eq in HeqCp'; trivial.

    exists (Cp' ++ revflatten Clp).
    simpl.
    split.

    * apply cache_beq_eq; trivial.
      rewrite <- app_assoc.
      subst c2.
      rewrite HeqCp'.
      apply app_eq_compat_l.
      apply cache_path_revflatten with (lp := lp); trivial.

      revert Clp HClp.
      clear.
      { induction lp as [ | p lp IH ];
        intros Clp HClp.

      - inversion HClp.
        constructor.

      - inversion HClp as [ | Ba Cp Bc Clp' [ Heqcache Hassoc ] Htl Bg Bh ].
        constructor; subst.

        + apply cache_beq_eq in Heqcache; trivial.
        + apply IH; trivial. }

    * intros t' Hassoct'.
      rewrite assoc_app_neq_None in Hassoct'.
      { destruct Hassoct' as [ Hassoct' | Hassoct' ].

      - assert (exists Clpf, cache_left p' = Clpf ++ c1) as [Clpf Heqcachep']. {
          exists (revflatten Clp).
          apply cache_path_revflatten with (Clp:= Clp) (lp:=lp); trivial.
          revert Clp HClp.
          clear.
          induction lp as [ | p lp IH ];
          intros Clp HClp.

          - inversion HClp; constructor.
          - inversion HClp as [ | Ba Cp Bc Clp' [ Heqcache Hassoc ] Htl Bg Bh ].
            constructor; subst.

            + apply cache_beq_eq in Heqcache; trivial.
            + apply IH; trivial.
        }
        generalize (HCp' t' Hassoct').
        rewrite Heqcachep'.
        intros Hassoc't'.
        apply assoc_app_eq_None with Clpf; trivial.

      - assert (exists Cp, In Cp Clp /\ assoc_cache t' Cp <> None) as (Cp & HinCp & Hassoc't'). {
          revert Hassoct'; clear; revert t' Clp; intros t Cs Hflat.
          induction Cs as [ | C Cs' IH ].
          - simpl in Hflat; tauto.
          - simpl in Hflat.
            apply assoc_app_neq_None in Hflat.
            destruct Hflat as [ Hflat | Hflat ].
            + apply IH in Hflat.
              destruct Hflat as ( Cp & HinCs & Hassoc ).
              exists Cp.
              split; simpl; tauto.
            + exists C.
              simpl; tauto.
        }
        apply in_split in HinCp; destruct HinCp as (Clp1 & Clp2 & HeqClp).
        rewrite HeqClp in HClp.
        apply Forall2_app_inv_r in HClp.
        destruct HClp as (lp1 & lp2 & HClp1 & HClp2 & Heqlp).
        inversion HClp2 as [ | p Bb lp2' Bd [ Heqcache Hassoc ] HClp2' Bg Bh ].
        subst.
        apply cache_path_app in Heqpath; trivial.
        destruct Heqpath as [ Heqpath1 Heqpath2 ].
        apply Hassoc in Hassoc't'.
        rewrite (cache_path_revflatten (Clp := Clp1) Heqpath1) in Hassoc't'.

        + apply assoc_app_eq_None in Hassoc't'.
          destruct Hassoc't'; assumption.

        + revert HClp1.
          clear;
          revert Clp1.
          induction lp1 as [ | p lp IH ]; intros Clp Hfor2.

          * inversion Hfor2; constructor.

          * inversion Hfor2 as [ | Ba Cp Bc Clp' [ Heqcache _ ] Hfor2' Bg Bh ]; subst.
            { constructor.
            - apply cache_beq_eq in Heqcache; assumption.
            - apply IH; tauto. }
      }

  + rewrite forall_andl.
    simpl in Hwf.
    destruct p' as [ | | i s p c1' t' c2' v'| c t' v' ]; try tauto;
    destruct t'; try tauto;
    destruct t; try tauto.

- (* cbv_update *)
  simpl in Hwf; destruct t as [ | | f lv ] in Hwf; try tauto.
  destruct Hwf as ( Hfc1 & _ & _ & _ & _ & _ & _ & _ & Hleftc1 & _ & Hrightc2 & Hwfp' & _).
  subst.
  simpl.
  destruct (IHp' Hwfp') as ( C1 & HC1 & HassocC1 ).
  apply cache_beq_eq in HC1; trivial.
  exists ((fapply f lv, v) :: C1).
  split.

  + simpl.
    repeat rewrite Bool.andb_true_iff.
    repeat split.

    * unfold function_beq.
      apply function_beq_refl.

    * apply list_beq_refl.
      intros; apply term_beq_eq; trivial.

    * apply value_beq_refl.

    * apply cache_beq_eq; trivial.

  + intros t' Hassoct'.
    simpl in Hassoct'.
    case_eq (term_beq t' (fapply f lv)).

    * rewrite term_beq_eq; trivial.
      intros; subst; trivial.

    * intros Hneq.
      rewrite Hneq in Hassoct'.
      apply HassocC1; trivial.

- (* cbv_read *)
  exists [].
  simpl; split.

  + apply cache_beq_eq; trivial.

  + tauto.
Qed.

Lemma cache_path_consistent c1 c2 lp :
  andl (map wf lp) ->
  cache_path c1 c2 lp = true ->
  forall p, In p lp ->
    exists c3,
      c2 = c3 ++ cache_right p /\
      (forall t, assoc_cache t c3 <> None -> assoc_cache t (cache_right p) = None).
Proof.
intros H_wf H_cache p Hp.
apply In_prefix_suffix in Hp.
destruct Hp as (lp1 & lp2 & Hlp).
subst lp.
rewrite cache_path_app in H_cache; trivial.
destruct H_cache as [ _ H_cache ].
simpl in H_cache.
rewrite Bool.andb_true_iff in H_cache.
destruct H_cache as [ _ H_cache ].
rewrite map_app, andl_app in H_wf.
destruct H_wf as[ _ H_wf ].
clear c1 lp1.
simpl in H_wf.
destruct H_wf as [ H_wf_p H_wf_lp2 ].

revert c2 H_cache.
induction lp2 as [ | p' lp2 IH ] using rev_ind; simpl; intros c2 H_cache.

- exists [].
  apply cache_beq_eq in H_cache; trivial.
  subst c2.
  tauto.

- rewrite map_app, andl_app in H_wf_lp2.
  destruct H_wf_lp2 as [ H_wf_lp2 H_wf_p' ].
  eapply IH with (c2 := cache_left p') in H_wf_lp2; clear IH.

  + simpl in H_wf_p'.
    destruct H_wf_p' as [ H_wf_p' _ ].
    apply cache_consistent in H_wf_p'.
    destruct H_wf_p' as (c3 & H1 & H2).
    rewrite cache_beq_eq in H1; trivial.
    rewrite cache_path_app in H_cache; trivial.
    destruct H_wf_lp2 as (c4 & H3 & H4).
    simpl in H_cache.
    rewrite Bool.andb_true_iff in H_cache.
    destruct H_cache as (H_cache & _ & H_cache').
    rewrite cache_beq_eq in H_cache'; trivial.
    subst c2.
    rewrite H3, H1 in *.
    exists (c3 ++ c4).
    split.

    * apply app_assoc.

    * intros t H5.
      apply assoc_app_neq_None in H5.
      destruct H5 as [ H5 | H5 ]; auto.
      apply H2 in H5.
      apply assoc_app_eq_None in H5.
      tauto.

  + rewrite cache_path_app in H_cache; trivial.
    tauto.
Qed.

Lemma cache_path_consistent_head C p lp :
  wf p -> andl (map wf lp) ->
  cache_path (cache_right p) C lp = true ->
    exists C',
      C = C' ++ cache_right p /\
      (forall t, assoc_cache t C' <> None -> assoc_cache t (cache_right p) = None).
Proof.
intros Hwfp Hwflp Hpath.
apply cache_path_consistent with (c1 := cache_left p) (lp := p::lp);
 simpl; try tauto.
apply andb_true_iff.
split; trivial.
apply cache_beq_refl.
Qed.

Lemma assoc_cache_hd (f: function) (lv: list term) (v: value) (C: cache) :
  assoc_cache (fapply f lv) ((fapply f lv, v) :: C) = Some v.
Proof.
  simpl.
  assert (function_beq function_eq_dec f f &&
          list_beq term term_beq lv lv = true)
    as Htrue.
  { apply andb_true_iff; split.
    - apply function_beq_refl.
    - apply list_beq_refl.
      intros; apply term_beq_eq; trivial.
  }
  rewrite Htrue.
  trivial.
Qed.

Definition valid_cache_extension (ext base: cache) : Prop :=
  forall t: term, assoc_cache t ext <> None -> assoc_cache t base = None.

Lemma cache_extension_app (ext' ext base: cache) :
  valid_cache_extension ext' (ext ++ base) ->
  valid_cache_extension ext base ->
  valid_cache_extension (ext' ++ ext) base.
Proof.
unfold valid_cache_extension.
intros H1 H2 t H3.
rewrite assoc_app_neq_None in H3.
destruct H3 as [ H3 | H3 ]; auto.
apply H1 in H3.
rewrite assoc_app_eq_None in H3.
tauto.
Qed.

Definition cbv_cache_entry (π : cbv) := (proj_left π, proj_right π).

(** ** Bounding caches *)

(** Lemma 21 *)
Lemma cache_content (π : cbv) :
  wf π ->
  cache_right π =
  map cbv_cache_entry (ℐᵃ_cache_order π) ++
      cache_left π.
Proof.
induction π as [lp c1 t c2 v IH_lp | lp p' c1 t c2 v IH_lp IH_p' | i s p' c1 t c2 v IH_p' | c t v] using cbv_ind2; simpl; intros Hwf.
- destruct t as [ | c lt | ]; try tauto;
  destruct v as [ c' lv ].
  destruct Hwf as (Hcachepath & _ & _ & _ & Hwflp & _).
  clear c c' lt lv.
  revert c1 c2 IH_lp Hcachepath Hwflp.
  induction lp as [ | p lp IH ]; intros c1 c2 IH_lp Hcachepath Hwflp; simpl in *.
  + apply cache_beq_eq in Hcachepath; try tauto.
    symmetry; assumption.
  + apply andb_true_iff in Hcachepath; destruct Hcachepath as [ Heqc1 Hcachepath ].
    apply cache_beq_eq in Heqc1; try tauto.
    destruct Hwflp as [ Hwfp Hwflp ].
    rewrite map_app; rewrite <- app_assoc.
    apply IH; try tauto.
    * intros; apply IH_lp; tauto.
    * replace (map cbv_cache_entry (ℐᵃ_cache_order p) ++ c1) with (cache_right p); try tauto.
      subst c1.
      apply IH_lp; tauto.
- rewrite map_app; rewrite <- app_assoc.
  assert (wf p' /\
          andl (map wf lp) /\
          cache_path c1 (cache_left p') lp = true /\
          cache_right p' = c2)
    as (Hwfp' & Hwflp & Hpathlp & Heqcachep'_r).
  {
      destruct p'; try tauto; destruct t0; try tauto; destruct t; try tauto;
      decompose record Hwf; auto.
  }

  assert (Heqcachep'_l : cache_left p' = map cbv_cache_entry (revflatten (map ℐᵃ_cache_order lp)) ++ c1).
  {
    clear c2 t v Hwf IH_p' Hwfp' Heqcachep'_r.
    revert c1 Hpathlp Hwflp IH_lp.
    induction lp as [ | p lp IH ]; intros c1 Hpathlp Hwflp IH_lp; simpl in *.
    - apply cache_beq_eq in Hpathlp; try tauto.
      symmetry; assumption.
    - apply andb_true_iff in Hpathlp; destruct Hpathlp as [ Heqc1 Hcachepath ].
      apply cache_beq_eq in Heqc1; try tauto.
      destruct Hwflp as [ Hwfp Hwflp ].
      rewrite map_app; rewrite <- app_assoc.
      apply IH; try tauto.
      + replace (map cbv_cache_entry (ℐᵃ_cache_order p) ++ c1) with (cache_right p); try tauto.
        subst c1.
        apply IH_lp; tauto.
      + intros; apply IH_lp; tauto.
  }
  rewrite <- Heqcachep'_l; rewrite <- Heqcachep'_r.
  apply IH_p'; tauto.
- destruct t; try tauto.
  destruct Hwf as (_ & _ & t & _ & _ & _ & _ & _ & Heqc1 & _ & Heqc2 & Hwf & _).
  subst c1 c2.
  f_equal.
  + apply IH_p'; trivial.
- intros; trivial.
Qed.

Lemma cache_content_on_path c1 c2 lp:
  andl (map wf lp) ->
  cache_path c1 c2 lp = true ->
  c2 = map cbv_cache_entry (revflatten (map ℐᵃ_cache_order lp)) ++ c1.
Proof.
  revert c1 c2; induction lp as [ | p lp IH ]; intros c1 c2 Hwf Hcachepath.

  - simpl; symmetry.
    simpl in Hcachepath.
    apply cache_beq_eq in Hcachepath; assumption.

  - simpl.
    rewrite map_app, <- app_assoc.
    apply IH.

    + destruct Hwf; assumption.

    + simpl in Hcachepath.
      apply andb_true_iff in Hcachepath.
      destruct Hcachepath as [ Heq Hcachepath ].
      apply cache_beq_eq in Heq; try assumption; subst c1.
      destruct Hwf;
      rewrite <- cache_content; assumption.
Qed.

Lemma cache_path_proj_left_in_tail_not_in_head t p lp c1 c2 :
  cache_path c1 c2 (p :: lp) = true ->
  andl (map wf (p :: lp)) ->
  In t (map proj_left (revflatten (map ℐᵃ_cache_order lp))) ->
  ~ In t (map proj_left (ℐᵃ_cache_order p)).
Proof.
  intros Hcachepath Hwf Hin.
  assert (Hleft_fst: forall t: cbv, proj_left t = fst (cbv_cache_entry t)).
  { clear; intros t; tauto. }
  rewrite map_ext with (g := fun t => fst (cbv_cache_entry t)); [ idtac | exact Hleft_fst ].
  rewrite <- map_map.
  apply assoc_None_not_in with (beq := term_beq);
    [ intros; apply term_beq_eq; assumption | idtac ].
  generalize Hcachepath; intros Hcachepath'.
  apply cache_path_consistent with  (p := p) in Hcachepath';
    try assumption; [ idtac | solve [apply in_eq] ].
  destruct Hcachepath' as ( c3 & Heqcache & Hassocs ).
  assert (Hassoc': assoc term_beq t (cache_right p) = None).
  { apply Hassocs.
    apply in_assoc_neq_None;
      [ intros a b Heq; rewrite term_beq_eq; try exact Heq; assumption | idtac ].
    simpl in Hcachepath.
    apply andb_true_iff in Hcachepath.
    destruct Hcachepath as [ Hcacheeq Hcachepath ].
    apply cache_content_on_path in Hcachepath ;
      [ idtac | simpl in Hwf; destruct Hwf; assumption ].
    subst c2.
    apply app_inv_tail in Heqcache.
    subst c3.
    rewrite map_map.
    simpl.
    assumption.
  }
  rewrite cache_content in Hassoc';
    try (destruct Hwf; assumption).
  rewrite assoc_app_eq_None in Hassoc'.
  destruct Hassoc'; assumption.
Qed.

Lemma whole_cache_path_consistent lp : forall c1 c2,
  cache_path c1 c2 lp = true ->
  andl (map wf lp) ->
  exists C,
    cache_beq c2 (C ++ c1) = true /\
    (forall t, assoc_cache t C <> None -> assoc_cache t c1 = None).
Proof.
  induction lp; intros c1 c2 H Hwf.
  - exists [].
    simpl.
    split.
    + simpl in H.
      apply cache_beq_eq in H; auto.
      rewrite H.
      apply cache_beq_eq; auto.

    + tauto.

  - simpl in H.
    apply andb_true_iff in H; destruct H as [Hl Hr].
    simpl in Hwf.
    destruct Hwf as [Hwfa Hwfl].
    destruct (cache_consistent Hwfa) as [C [HCr HCl]].
    apply cache_beq_eq in HCr; auto.
    apply cache_beq_eq in Hl; auto.
    rewrite <- Hl in *.
    destruct (IHlp (cache_right a) c2 Hr Hwfl) as [C' [HC'1 HC'2]].
    apply cache_beq_eq in HC'1; auto.
    rewrite HCr in *.
    rewrite app_assoc in HC'1.
    exists (C'++C).
    split.
    + apply cache_beq_eq; assumption.

    + intros t Ht.
      apply assoc_app_neq_None in Ht.
      destruct Ht.
      * pose (HC'2 t H) as Htt.
        apply assoc_app_eq_None in Htt.
        destruct Htt; auto.

      * exact (HCl t H).
Qed.

Lemma cache_path_proj_left_not_in_init t lp c1 c2 :
  cache_path c1 c2 lp = true ->
  andl (map wf lp) ->
  In t (map proj_left (revflatten (map ℐᵃ_cache_order lp))) ->
  ~ In t (map fst c1).
Proof.
  intros Hcachepath Hwf Hin.
  apply assoc_None_not_in with (beq := term_beq);
    [ intros; apply term_beq_eq; assumption | idtac ].
  generalize Hwf;
    intros Hconsistent;
    apply whole_cache_path_consistent with (c1 := c1) (c2 := c2) in Hconsistent;
    [ idtac | assumption ].
  destruct Hconsistent as (c3 & Heq & Hassoc).
  apply Hassoc.
  apply in_assoc_neq_None;
    [ intros; apply term_beq_eq; assumption | idtac ].
  apply cache_beq_eq in Heq; try assumption.
  apply cache_content_on_path in Hcachepath; [ idtac | exact Hwf ].
  subst c2.
  apply app_inv_tail in Heq.
  subst c3.
  rewrite map_map.
  simpl.
  exact Hin.
Qed.

Lemma cache_lookup_term (p: cbv) (ext: cache):
  wf p ->
  (forall t: term, assoc_cache t ext <> None -> assoc_cache t (cache_right p) = None) ->
  cache_lookup (ext ++ cache_right p) (proj_left p) = @term_from_value _ _ _ (proj_right p).
Proof.
  revert ext.
  induction p as [ lp c1 t c2 v IHlp | lp p' c1 t c2 v IHlp IHp | i s p' c1 t c2 v IHp | c t v ] using cbv_ind2;
    intros ext Hwf Hext.

  - (* cbv_constr *)
    generalize Hwf; intros Hcache; apply cache_content in Hcache.
    simpl in *.
    destruct t as [ | c lt | ]; try tauto.
    destruct v as [ c' lv ].
    destruct Hwf as (Hpath & Heqc' & Heqlt & Heqlv & Hwflp & _).
    subst c' lt lv.
    simpl.
    f_equal; trivial.
    do 2 rewrite map_map.
    revert c1 Hpath Hcache.
    induction lp as [ | p lp IHlp' ]; trivial; intros c1 Hpath Hcache.
    simpl.
    f_equal.

    + clear IHlp'.
      assert (Hin : In p (p::lp)); [simpl; left; trivial | idtac ].
      destruct (cache_path_consistent Hwflp Hpath Hin)
      as (extp & Heqextp & Hextp).
      rewrite Heqextp.
      replace (ext ++ extp ++ cache_right p) with ((ext ++ extp) ++ cache_right p);
      [ idtac | rewrite <- app_assoc; trivial ].
      apply IHlp; trivial; simpl in Hwflp; try tauto.
      * apply cache_extension_app; trivial.
        rewrite Heqextp in Hext.
        trivial.

    + simpl in *.
      apply andb_true_iff in Hpath.
      destruct Hpath as [ Heqc1 Hpath ].
      apply cache_beq_eq in Heqc1; trivial.
      apply IHlp' with (c1 := cache_right p); auto with *; simpl in Hwflp; try tauto.
      clear IHlp'.
      rewrite Hcache, map_app, <- app_assoc.
      clear Hcache.
      f_equal.
      subst c1.
      symmetry; apply cache_content; trivial; tauto.

  - (* cbv_split *)
    generalize Hwf; intros Hcache; apply cache_content in Hcache.
    simpl in Hwf.
    destruct p' as [ | | i s p' c1' t' c2' v' | c t' v' ]; try tauto;
      destruct t' as [ | | f' lv' ]; try tauto;
      destruct t as [ | | f lt ]; try tauto.

    + (* p' = cbv_update *)
      destruct Hwf as ( Heqc2 & Hpath & Heqlt & Heqlv' & Hwflp & Heqf & Heqv & Hwfp' & _).
      assert (Hlookuplt : map (cache_lookup (ext ++ c2)) lt = lv').
      { rewrite Heqlt.
        rewrite Heqlv'.
        subst f' v' c2'.
        apply cache_consistent in Hwfp'.
        destruct Hwfp' as (ext' & Heqc2 & Hext').
        rewrite cache_beq_eq in Heqc2; try tauto; simpl in Heqc2.
        simpl in Hcache.
        rewrite Heqc2.
        set (ext'' := ext ++ ext').
        assert (Hvalidext : valid_cache_extension ext'' c1').
        { apply cache_extension_app.
          - rewrite Heqc2 in Hext.
            assumption.
          - assumption.
        }
        clear lt Hext Hext' Hcache Heqc2 Heqlt Heqlv'.
        replace (ext ++ ext' ++ c1') with (ext'' ++ c1');
          [ idtac | unfold ext''; rewrite <- app_assoc; trivial ].
        revert c1 Hpath IHlp Hwflp.
        induction lp as [ | p lp IH ]; intros c1 Hpath IHlp Hwflp.

        - simpl; trivial.

        - simpl; f_equal.

          + assert (Hin : In p (p::lp)); [simpl; left; trivial | idtac ].
            destruct (cache_path_consistent Hwflp Hpath Hin)
              as (extp & Heqextp & Hextp).
            rewrite Heqextp.
            replace (ext'' ++ extp ++ cache_right p) with ((ext'' ++ extp) ++ cache_right p);
              [ idtac | rewrite <- app_assoc; trivial ].
            apply IHlp.
            * simpl; trivial.
            * simpl in Hwflp; tauto.
            * apply cache_extension_app; subst c1'; assumption.

          + destruct Hwflp as [ _ Hwflp ].
            simpl in Hpath; rewrite andb_true_iff in Hpath; destruct Hpath as [ _ Hpath ].
            apply IH with (c1 := cache_right p); trivial.
            intros; apply IHlp; simpl; tauto.
      }
      subst f' v' c2'.
      simpl; simpl in Hcache. unfold cbv_cache_entry at 1 in Hcache; simpl in Hcache.
      rewrite Hlookuplt.
      assert (Heqv : assoc_cache (fapply f lv') (ext ++ c2) = Some v).
      { simpl in Hext.
        case_eq (assoc_cache (fapply f lv') ext).
        - (* absurd case: f(lv') in ext *)
          intros v' HextSome.
          generalize (Hext (fapply f lv')); intros Hextf.
          rewrite HextSome in Hextf.
          assert (Hneq : Some v' <> None).
          + discriminate.
          + apply Hextf in Hneq.
            subst c2.
            rewrite assoc_cache_hd in Hneq.
            discriminate.

        - intros.
          apply assoc_app_eq_Some; right; split; [ assumption | idtac ].
          subst c2.
          rewrite assoc_cache_hd.
          trivial.
      }
      rewrite Heqv.
      tauto.

    + (* p' = cbv_read *)
      destruct Hwf as (Heqc & Hpath & Heqlt & Heqlv' & Hwflp & Heqf & Heqv & Hwfp' & _).
      assert (Hlookuplt : map (cache_lookup (ext ++ c2)) lt = lv').
      { rewrite Heqlt.
        rewrite Heqlv'.
        subst f' v' c2.
        simpl in Hcache.
        simpl in Hext.
        clear lt Hcache Heqlt Heqlv'.
        revert c1 Hpath IHlp Hwflp.
        induction lp as [ | p lp IH ]; intros c1 Hpath IHlp Hwflp.

        - simpl; trivial.

        - simpl; f_equal.

          + assert (Hin : In p (p::lp)); [simpl; left; trivial | idtac ].
            destruct (cache_path_consistent Hwflp Hpath Hin)
              as (extp & Heqextp & Hextp).
            rewrite Heqextp.
            replace (ext ++ extp ++ cache_right p) with ((ext ++ extp) ++ cache_right p);
              [ idtac | rewrite <- app_assoc; trivial ].
            apply IHlp.
            * simpl; trivial.
            * simpl in Hwflp; tauto.
            * apply cache_extension_app; subst c; assumption.

          + destruct Hwflp as [ _ Hwflp ].
            simpl in Hpath; rewrite andb_true_iff in Hpath; destruct Hpath as [ _ Hpath ].
            apply IH with (c1 := cache_right p); trivial.
            intros; apply IHlp; simpl; tauto.
      }
      simpl in *.
      destruct Hwfp' as [ Hassoc _ ].
      subst c f' v'.
      rewrite Hlookuplt.
      assert (Heqv : assoc_cache (fapply f lv') (ext ++ c2) = Some v).
      { case_eq (assoc_cache (fapply f lv') ext).
        - (* absurd case: f(lv') in ext *)
          intros v' HextSome.
          generalize (Hext (fapply f lv')); intros Hextf.
          rewrite HextSome in Hextf.
          assert (Hneq : Some v' <> None).
          + discriminate.
          + apply Hextf in Hneq.
            rewrite Hassoc in Hneq.
            discriminate.
        - intros.
          apply assoc_app_eq_Some; right; split; assumption.
      }

      rewrite Heqv.
      trivial.

  - (* cbv_update *)
    simpl; simpl in Hwf.
    destruct t as [ | | f lv ]; try tauto.
    destruct Hwf as ( Hassoc_l & lp & t & _ & _ & Heqlv & Heqp'_l & Heqp'_r & Heqc1 & _ & Heqc2 & Hwf & _).
    simpl.
    replace (map (cache_lookup (ext ++ c2)) lv) with lv.
    + assert (assoc_cache (fapply f lv) (ext ++ c2) = Some v) as HcacheSome.
      {
        case_eq (assoc_cache (fapply f lv) ext).
        - intros v' HextSome.
          generalize (Hext (fapply f lv)); simpl; rewrite HextSome; intros HextneqNone.
          assert (Hneq : Some v' <> None); [ discriminate | idtac ].
          apply HextneqNone in Hneq.
          rewrite Heqc2, assoc_cache_hd in Hneq.
          discriminate.
        - intros HextNone.
          apply assoc_app_eq_Some; right; split; trivial.
          subst c2.
          apply assoc_cache_hd.
      }
      rewrite HcacheSome.
      trivial.

    + rewrite Heqlv.
      symmetry; apply map_cache_lookup_value.

  - (* cbv_read *)
    simpl in Hwf.
    destruct t as [ | | f lv ]; try tauto.
    destruct Hwf as ( Hassoc & lv' & Heqlv ).
    simpl.
    replace (map (cache_lookup (ext ++ c)) lv) with lv.

    + assert (assoc_cache (fapply f lv) (ext ++ c) = Some v) as HcacheSome.
      {
        case_eq (assoc_cache (fapply f lv) ext).
        - intros v' HextSome.
          generalize (Hext (fapply f lv)); simpl; rewrite HextSome; intros HextneqNone.
          assert (Hneq : Some v' <> None); [ discriminate | idtac ].
          apply HextneqNone in Hneq.
          rewrite Hassoc in Hneq.
          discriminate.
        - intros HextNone.
          apply assoc_app_eq_Some; right; split; trivial.
      }
      rewrite HcacheSome.
      trivial.

    + rewrite Heqlv.
      symmetry; apply map_cache_lookup_value.
Qed.

Lemma first_activations_residues_activation i s p c1 t c2 v :
  let π := cbv_update i s p c1 t c2 v in
  wf π ->
  Forall2 (fun p' t' =>
    match (proj_left p', t') with
    | (fapply f lv, fapply f' lt) =>
      f = f' /\
      Forall2 (fun t v => cache_lookup (cache_left p') t = v) lt lv
    | _ => False
    end)
    (first_activations_and_semi π)
    (fapplies_in_term (proj_left p)).
Proof.
intros π H_wf.
unfold first_activations_and_semi.
simpl.
remember (proj_left p) as t' eqn: H_t'_proj.
unfold π in H_wf.
assert (wf p) as Hwf_p.
{
  simpl in H_wf.
  destruct t as [ | | f lv ]; try tauto.
  decompose record H_wf; auto.
}
generalize p H_t'_proj Hwf_p ; clear i s p c1 t c2 v π H_wf H_t'_proj Hwf_p.
induction t' as [ | c lt IH | f lt IH ] using term_ind2; intros p H_t_proj Hwf_p.

- destruct p as [ lp c1 t c2 v | lp p' c1 t c2 v | i s p' c1 t c2 v | c t v ]; simpl in *; subst; try tauto.
  destruct p' as [ lp' c1' t c2' v' | lp' p' c1' t c2' v' | i' s' p' c1' t c2' v' | c' t v' ]; try tauto;
  destruct t; tauto.

- destruct p as [ lp c1 t c2 v | lp p' c1 t c2 v | i s p' c1 t c2 v | c' t v ];
  simpl in *;
  subst;
  try (try tauto;
       destruct p' as [ lp' c1' t c2' v' | lp' p' c1' t c2' v' | i' s' p' c1' t c2' v' | c' t v' ];
       try tauto;
       destruct t;
       tauto).

  apply Forall2_flat_map.
  destruct v as [ c' lv ].
  destruct Hwf_p as (_ & Heqc & Heqlt & _ & Hwflp & _).
  subst c' lt.
  induction lp as [ | p lp IH' ];
    constructor;
    simpl in Hwflp;
    destruct Hwflp as (Hwfp & Hwflp).

  + apply IH; trivial.
    simpl; tauto.

  + apply IH'; trivial.
    clear IH'.
    simpl in *.
    intros t Hinlp.
    apply IH.
    tauto.

- destruct p as [ lp c1 t c2 v | lp p' c1 t c2 v | i s p' c1 t c2 v | c t v ].

  + simpl in Hwf_p.
    destruct t as [ | c' lt' | ]; try tauto.
    destruct v as [ c'' lv'' ].
    simpl in H_t_proj.
    discriminate H_t_proj.

  + simpl.
    simpl in Hwf_p.
    assert (first_activations_and_semi_rec p' = [p']) as Hp'. {
    repeat match goal with
           | _ : match ?x with _ => _ end |- _ => destruct x; try tauto
           end.
    }
    simpl in H_t_proj; subst t.
    rewrite Hp'; constructor.

    * assert ( exists f' lv,
               proj_left p' = fapply f' lv /\
               cache_path c1 (cache_left p') lp = true /\
               lt = map proj_left lp /\
               lv = map (@term_from_value _ _ _) (map proj_right lp) /\
               andl (map wf lp) /\
               f' = f /\
               wf p' ) as ( f' & lv & Heqprojp' & Hcachepath_lp & Heqlt & Heqlv & Hwflp & Heqf & Hwfp' ).
      {
        repeat match goal with
               | _ : match ?x with _ => _ end |- _ => destruct x; try tauto
               end; eexists; eexists; tauto.
      }
      clear Hwf_p.
      rewrite Heqprojp'; split; trivial.
      clear IH Hp'.
      subst f'.
      assert (Forall (fun p => forall ext, (forall t: term, assoc_cache t ext <> None -> assoc_cache t (cache_right p) = None) -> cache_lookup (ext ++ cache_right p) (proj_left p) = @term_from_value _ _ _ (proj_right p)) lp /\
              Forall (fun p => exists ext, (forall t: term, assoc_cache t ext <> None -> assoc_cache t (cache_right p) = None) /\ cache_left p' = ext ++ cache_right p) lp) as [ Hforlook Hcache ]. {
        split.
        - clear f v c2 Heqprojp' Hwfp'.
          revert lt lv c1 Hcachepath_lp Heqlt Heqlv Hwflp.
          induction lp as [ | p lp IH ]; intros lt lv C Hcachepath Heqlt Heqlv Hwflp; constructor; simpl in *.
          + intros ext.
            apply cache_lookup_term.
            tauto.
          + apply IH with (lt := map proj_left lp)
                          (lv := map (@term_from_value _ _ _)
                                    (map proj_right lp))
                          (c1 := cache_right p);
            trivial; try tauto.
            rewrite Bool.andb_true_iff in Hcachepath.
            tauto.
        - clear f v c2 Heqprojp' Hwfp'.
          revert lt lv c1 Hcachepath_lp Heqlt Heqlv Hwflp.
          induction lp as [ | p lp IH ]; intros lt lv C Hcachepath Heqlt Heqlv Hwflp.
          + constructor.
          + constructor; simpl in *.
            * destruct Hwflp as [ Hwfp Hwflp ].
              rewrite Bool.andb_true_iff in Hcachepath.
              destruct Hcachepath as [ Heqcache Hcachepath ].
              destruct (cache_path_consistent_head Hwfp Hwflp Hcachepath) as [ lC H ].
              exists lC.
              tauto.
            * apply IH with (lt := map proj_left lp)
                            (lv := map
                                    (@term_from_value _ _ _)
                                    (map proj_right lp))
                            (c1 := cache_right p);
              trivial; try tauto.
              rewrite Bool.andb_true_iff in Hcachepath.
              tauto.
      }
      clear Hcachepath_lp Hwfp' Heqprojp' f c1 c2 v.
      revert lt lv Heqlt Heqlv Hforlook Hcache Hwflp.
      { induction lp as [ | p lp IH ]; simpl; intros lt lv Heqlt Heqlv Hforlook Hcache Hwflp; subst; constructor.
        - inversion Hforlook as [ | p'' lp'' Hforlookp ]; subst.
          inversion Hcache as [ | p''' lp''' Hcachep ]; subst.
          destruct Hcachep as (ext & Hext & Heqcache).
          rewrite Heqcache.
          apply Hforlookp.
          trivial.
        - apply IH; trivial; try tauto.
          + inversion Hforlook; trivial.
          + inversion Hcache; trivial.
      }

    * apply Forall2_flat_map.
      assert ( exists f0 lv,
               lt = map proj_left lp /\
               lv = map (@term_from_value variable function _) (map proj_right lp) /\
               andl (map wf lp) /\
               f0 = f /\ wf p') as ( f0 & lv & Heqlt & Heqlv & Hwflp & Heqf & Hwfp ).
      {
        repeat match goal with
               | _ : match ?x with _ => _ end |- _ => destruct x; try tauto
               end; eexists; eexists; tauto.
      }
      subst.
      clear Hwf_p Hwfp.
      { induction lp as [ | p lp IH' ];
        constructor;
        destruct Hwflp as (Hwfp & Hwflp).

      - apply IH; trivial.
        simpl; tauto.

      - apply IH'; trivial.
        clear IH'.
        simpl in *.
        intros t Hinlp.
        apply IH.
        tauto. }

  + simpl first_activations_and_semi_rec; simpl fapplies_in_term.
    constructor.

    * simpl.
      simpl in H_t_proj.
      subst.
      split; trivial.
      simpl in Hwf_p; destruct Hwf_p as ( _ & lp & _ & _ & _ & Hval & _).
      revert Hval; clear.
      remember (map (psubst s) lp) as lv eqn: Heqlv.
      clear Heqlv. revert lv.
      { induction lt as [ | t lt IH ]; constructor.

      - destruct lv as [ | v lv ] ; try discriminate;
        injection Hval; intros; subst.
        apply cache_lookup_value.

      - destruct lv as [ | v lv ] ; try discriminate;
        injection Hval; intros; subst.
        eapply IH.
        reflexivity.
      }

    * simpl in Hwf_p.
      destruct t as [ | | f' lv' ]; try tauto.
      simpl in H_t_proj; injection H_t_proj; intros x1 x2; subst; clear H_t_proj.

      replace (flat_map (@fapplies_in_term _ _ _) lv') with ([]: list term); try constructor.

      destruct Hwf_p as (_ & lp & _ & _ & _ & Hlv'_val & _).
      remember (map (psubst s) lp) as lv eqn: HBid.
      clear HBid.
      revert lv Hlv'_val.
      clear.
      induction lv' as [ | v' lv' IH ]; trivial.
      simpl.
      intros lv Heq.
      destruct lv; try discriminate Heq.
      rewrite map_cons in Heq.
      injection Heq; intros Heqlv Heqv; subst.
      rewrite <- IH with lv; trivial.
      rewrite fapplies_in_value_nil; trivial.

  + destruct t as [| | f' lt'] ; simpl in Hwf_p; try tauto.
    simpl in *.
    injection H_t_proj; intros; subst f' lt'; clear H_t_proj.
    destruct Hwf_p as (_ & lv & Heq).

    constructor.

    * simpl.
      split; trivial.
      subst lt.
      clear.
      induction lv as [ | v lv IH ]; constructor; trivial.
      apply cache_lookup_value.

    * subst lt.
      rewrite <- flat_map_comp with (h:= fun t => fapplies_in_term (@term_from_value _ _ _ t)); trivial.
      clear.
      replace (flat_map (fun t : value => fapplies_in_term (@term_from_value variable function constructor t)) lv)
        with ([]:list term);
        try constructor.
      rewrite flat_map_nil; trivial.
      intros v Hinlv.
      apply fapplies_in_value_nil.
Qed.

Lemma nb_nodes_bound i s p' c1 t c2 v :
  let p := cbv_update i s p' c1 t c2 v in
  #ℐᵃ⁺ᵖ p <= suml (map #𝓓 (ℐᵃ p)) + 𝓐 p.
Proof.
intro p.
pattern p. unfold 𝓐.
apply cbv_big_induction.
clear p.
intros i' s' p'' c1' t' c2' v' IH.
rewrite ℐᵃ_first_activations.
simpl in *.
rewrite <- plus_n_Sm.
apply le_n_S.
transitivity (#𝓓' p'' + suml (map nb_nodes (first_activations_rec p''))).

- clear IH.
  induction p'' as [ [ | p lp ] c1'' t'' c2'' v'' IH_lp | lp p c1'' t'' c2'' v'' IH_lp IH_p | i'' s'' p c1'' t'' c2'' v'' IH_p | c t'' v'' ] using cbv_ind2;
   simpl; trivial; try omega.

  + apply le_n_S.
    apply suml_map_le in IH_lp.
    simpl in IH_lp.
    etransitivity.

    * apply IH_lp.

    * clear IH_lp.
      rewrite map_app, suml_app, suml_map_plus, <- suml_flat_map_map, map_flat_map.
      omega.

  + apply le_n_S.
    apply suml_map_le in IH_lp.
    etransitivity.

    * {apply plus_le_compat.

      - apply IH_p.

      - apply IH_lp. }

    * clear IH_p IH_lp.
      rewrite map_app, suml_app, suml_map_plus, <- suml_flat_map_map, map_flat_map.
      omega.

- rewrite <- plus_assoc.
  apply plus_le_compat_l.
  transitivity (
    suml (map (fun x => suml (map #𝓓 (ℐᵃ x)) + length (ℐᵃ x)) (first_activations_rec p''))).

  + apply suml_map_le.
    intros p Hp.
    apply IH; trivial.

  + clear IH. simpl.
    rewrite length_flat_map, suml_map_plus, map_map, map_flat_map, suml_flat_map_map.
    trivial.
Qed.

Lemma nb_judgements_bound i s p' c1 t c2 v :
  let p := cbv_update i s p' c1 t c2 v in
  #ℐ p <= suml (map #𝓓 (ℐᵃ p)) + 𝓐 p + #ℐˢ p.
Proof.
induction p' as [ lp c1' t' c2' v' IH1 | lp p c1' t' c2' v' IH1 IH2 | i' s' p c1' t' c2' v' IH | c t' v' ] using cbv_ind2; simpl in *.

- simpl. rewrite <- plus_n_Sm.
  do 2 apply le_n_S.
  fold plus.
  assert (forall p, In p lp ->
      #ℐ p <= #𝓓' p + suml (map #𝓓 (ℐᵃ p)) +𝓐 p + #ℐˢ p
  ) as H. {
    intros p Hp.
    generalize (IH1 p Hp).
    simpl. omega.
  }
  clear IH1.
  apply suml_map_le in H.
  etransitivity; [eexact H | idtac].
  clear H.
  do 3 rewrite suml_map_plus.
  rewrite length_flat_map, map_map, map_flat_map, suml_flat_map, map_map.
  trivial.

- rewrite <- plus_n_Sm.
  do 2 apply le_n_S.
  fold plus.
  assert (forall p0 : cbv, In p0 lp ->
      #ℐ p0 <= #𝓓' p0 + suml (map #𝓓 (ℐᵃ p0)) + 𝓐 p0 + #ℐˢ p0) as H1. {
    intros p' Hp.
    generalize (IH1 p' Hp).
    simpl. omega.
  }
  assert (#ℐ p <= #𝓓' p + suml (map #𝓓 (ℐᵃ p)) + 𝓐 p + #ℐˢ p) as H2.
  simpl. omega.
  clear IH1 IH2.
  apply suml_map_le in H1.
  etransitivity.

  + apply plus_le_compat.

    * eexact H2.

    * eexact H1.

  + clear H1 H2.
  do 3 rewrite suml_map_plus.
  rewrite app_length, map_app, suml_app, length_flat_map, map_map, map_flat_map, suml_flat_map, map_map.
  simpl. omega.

- omega.

- trivial.
Qed.

Lemma nb_nb_judgement_rec_bound p :
  wf p -> #𝓓' p <= ╎proj_left p╎.
Proof.
intros H_wf_p.
induction p as [ lp c1 t c2 v IH | lp p c1 t c2 v IH _ | n s p c1 t c2 v _  | c t v ] using cbv_ind2; simpl in *.

- destruct t as [ | c lt | ]; try tauto.
  destruct v as [ c' lv ].
  simpl.
  apply le_n_S.
  destruct H_wf_p as (_ & _ & H_lt & _ & H_wf & _); clear c'.
  subst lt.
  rewrite map_map.
  apply suml_map_le.
  intros p H_p.
  apply IH.
  trivial.
  apply andl_in with (map wf lp).
  trivial.
  rewrite in_map_iff.
  exists p.
  tauto.

- destruct p as [ | | i s p c1' t' c2' v' | c t' v' ]; try tauto.

  + destruct t' as [ | | f lt]; try tauto.
    destruct t as [ | | f' lt']; try tauto.
    simpl in *.
    apply le_n_S.
    destruct H_wf_p as (H1 & H2 & H3 & H4 & H5 & lp' & t & (H6 & lp'' & t' & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16) & _).
    subst c2' lt' lt f' v' c1' c2.
    rewrite map_map.
    apply suml_map_le.
    intros p' H_p'.
    apply IH.
    trivial.
    apply andl_in with (map wf lp).
    trivial.
    rewrite in_map_iff.
    exists p'.
    tauto.

  + destruct t' as [ | | f lv]; try tauto.
    destruct t as [ | | f' lt]; try tauto.
    simpl in *.
    apply le_n_S.
    destruct H_wf_p as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
    subst lt lv f' v'.
    rewrite map_map.
    apply suml_map_le.
    intros p' H_p'.
    apply IH.
    trivial.
    apply andl_in with (map wf lp).
    trivial.
    rewrite in_map_iff.
    exists p'.
    tauto.

- apply le_0_n.

- apply le_0_n.
Qed.

Lemma nb_ℐᵖ_bound i s p c1 t c2 v :
  wf (cbv_update i s p c1 t c2 v) ->
  #𝓓 (cbv_update i s p c1 t c2 v) <= 𝓡 prog (╎t╎).
Proof.
intros H_wf_π.
assert (In (cbv_update i s p c1 t c2 v) (ℐᵃ (cbv_update i s p c1 t c2 v))) as H_p_activation.

- simpl; tauto.

- generalize (ℐᵃ_wf H_wf_π H_p_activation); intro H_wf_p.
  generalize (𝓡_spec s H_wf_π H_p_activation).
  simpl; intro H.
  transitivity (╎subst s (rhs_of_rule (nth i prog rule_default))╎); [clear H | trivial].
  transitivity (╎proj_left p╎).

  + apply nb_nb_judgement_rec_bound; trivial.
    apply (wf_cbv_update H_wf_p).

  + simpl in H_wf_p.
    destruct t; try tauto.
    destruct H_wf_p as (_ & lp & t & _ & H_rule & _ & H_proj & _).
    rewrite H_rule, H_proj; simpl.
    trivial.
Qed.

Lemma right_from_activation_or_from_left p : wf p ->
  maxl (map (fun tv : term * value => value_size (snd tv)) (cache_right p)) <=
  max (𝓢 p) (maxl (map (fun tv : term * value => value_size (snd tv)) (cache_left p))).
Proof.
intro H_wf.
induction p as [ lp c1 t c2 v IH_lp | lp p c1 t c2 v IH_lp IH_p | n s p c1 t c2 v IH_p  | c t v ] using cbv_ind2; simpl in *.

- destruct t as [ | c lt | ]; try tauto.
  destruct v as [ c' lv ].
  destruct H_wf as (H1 & H2 & H3 & H4 & H5 & _).
  subst c' lt lv.
  revert c1 c2 H1.
  induction lp as [ | p lp IH ]; simpl in *; intros c1 c2 H1.

  + apply cache_beq_eq in H1.
    subst c2.
    trivial.

  + rewrite andb_true_iff in H1.
    destruct H1 as [H1 H2].
    apply cache_beq_eq in H1.
    subst c1.
    apply IH in H2.

    * clear IH.
      etransitivity; try apply H2.
      {etransitivity.

      - apply NPeano.Nat.max_le_compat_l.
        apply IH_lp; tauto.

      - rewrite max_comm.
        do 2 rewrite <- max_assoc.
        apply NPeano.Nat.max_le_compat_l.
        rewrite max_comm.
        trivial. }

    * auto.

    * tauto.

- destruct p as [ | | i s p c1' t' c2' v' | c t' v' ]; try tauto.

  + destruct t' as [ | | f lv ]; try tauto.
    destruct t as [ | | f' lt ]; try tauto.
    destruct H_wf as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & _).
    subst c2' lt lv f' v'.
    apply IH_p in H8.
    clear IH_p.
    simpl in H8.
    etransitivity; [eexact H8 | clear H8].
    simpl.
    match goal with
    | |- max ?x _ <= _ => set (a := x)
    end.
    rewrite <- max_assoc.
    apply NPeano.Nat.max_le_compat_l.
    clear a.
    revert c1 H2.
    induction lp as [ | p' lp IH ]; simpl in *; intros c1 H2.

    *  apply cache_beq_eq in H2.
        subst c1'.
        trivial.

    * rewrite andb_true_iff in H2.
      destruct H2 as [H1 H2].
      apply cache_beq_eq in H1.
      subst c1.
      {apply IH in H2.

      - clear IH.
        etransitivity; [apply H2 | clear H2].
        rewrite (max_comm (𝓢 p')), <- max_assoc.
        apply NPeano.Nat.max_le_compat_l.
        apply IH_lp; tauto.

      - auto.

      - tauto. }

  + destruct t' as [ | | f lv ]; try tauto.
    destruct t as [ | | f' lt ]; try tauto.
    destruct H_wf as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & _).
    subst c2 lt lv f' v'.
    apply IH_p in H8.
    clear IH_p.
    etransitivity; [eexact H8 | clear H8].
    match goal with
    | |- max ?x _ <= _ => set (a := x)
    end.
    rewrite <- max_assoc.
    apply NPeano.Nat.max_le_compat_l.
    clear a.
    revert c1 H2.
    induction lp as [ | p' lp IH ]; simpl in *; intros c1 H2.

    *  apply cache_beq_eq in H2.
        subst c1.
        trivial.

    * rewrite andb_true_iff in H2.
      destruct H2 as [H1 H2].
      apply cache_beq_eq in H1.
      subst c1.
      {apply IH in H2.

      - clear IH.
        etransitivity; [apply H2 | clear H2].
        rewrite (max_comm (𝓢 p')), <- max_assoc.
        apply NPeano.Nat.max_le_compat_l.
        decompose record H5; auto.

      - auto.

      - tauto. }

- destruct t as [ | | f lv ]; try tauto.
  destruct H_wf as (H1 & lp & t & H2 & H3 & H4 & H5 & H6 & H7 & _ & H9 & H10 & _).
  subst lv v c1 c2.
  apply IH_p in H10.
  clear IH_p.
  simpl.
  destruct (𝓢 p) as [ | m ]; lia.

- apply le_n.
Qed.

Lemma right_from_activation_or_from_left_path lp c1 c2 : andl (map wf lp) ->
  cache_path c1 c2 lp = true ->
  maxl (map (fun tv : term * value => value_size (snd tv)) c2) <=
  max (maxl (map 𝓢 lp)) (maxl (map (fun tv : term * value => value_size (snd tv)) c1)).
Proof.
revert c1.
induction lp as [ | p lp IH]; simpl.

- intros c1 _ H1.
  rewrite cache_beq_eq in H1.
  subst c2.
  trivial.

- intros c1 [H1 H2] H3.
  rewrite andb_true_iff in H3.
  destruct H3 as [H3 H4].
  rewrite cache_beq_eq in H3.
  subst c1.
  apply IH in H4; trivial.
  clear IH.
  etransitivity; [apply H4 | clear H4].
  rewrite (max_comm (𝓢 p)), <- max_assoc.
  apply NPeano.Nat.max_le_compat_l.
  apply right_from_activation_or_from_left.
  trivial.
Qed.

Lemma value_size_bounded_by_nb_judgements p :
  wf p -> value_size (proj_right p) <= (1 + max (𝓢 p) (maxl (map (fun tv => value_size (snd tv)) (cache_left p)))) * #ℐ p.
Proof.
intro H.
induction p as [ lp c1 t c2 v IH | lp p c1 t c2 v IH_lp IH_p | n s p c1 t c2 v IH | c t v ] using cbv_ind2; simpl in *.

- destruct t as [ | c lt | ]; try tauto.
  destruct v as [ c' lv ].
  destruct H as (H1 & H2 & H3 & H4 & H5 & _).
  subst c' lt lv.
  simpl.
  apply le_n_S.
  rewrite map_map.
  transitivity (
    suml (map (fun p => #ℐ p +
     max (𝓢 p)
       (maxl
          (map (fun tv : term * value => value_size (snd tv)) (cache_left p))) *
     #ℐ p) lp)
  ).

  + apply suml_map_le.
    intros p H2.
    apply IH; trivial.
    apply andl_in with (map wf lp); trivial.
    apply in_map_iff.
    eauto.

  + clear IH.
    rewrite suml_map_plus.
    apply plus_le_compat_l.
    revert c1 H1.
    induction lp as [ | p lp IH]; simpl; intros c1 H1; try omega.
    rewrite andb_true_iff in H1.
    destruct H1 as [H1 H2].
    apply cache_beq_eq in H1.
    subst c1.
    simpl in H5.
    apply IH in H2; try tauto.
    clear IH.
    etransitivity.

    * apply plus_le_compat_l.
      apply H2.

    * clear H2.
      do 2 rewrite mult_succ_r.
      set (a := map #ℐ lp).
      set (b := map 𝓢 lp).
      set (d := 𝓢 p).
      set (e := map (fun tv : term * value => value_size (snd tv)) (cache_left p)).
      set (f := map (fun tv : term * value => value_size (snd tv)) (cache_right p)).
      {transitivity (max d (maxl e) * #ℐ p + (max (maxl b) (max d (maxl e)) * suml a + max (maxl b) (max d (maxl e)))).

      - apply plus_le_compat_l.
        apply plus_le_compat.

        + apply mult_le_compat_r.
          apply NPeano.Nat.max_le_compat_l.
          apply right_from_activation_or_from_left; tauto.

        + apply NPeano.Nat.max_le_compat_l.
          apply right_from_activation_or_from_left; tauto.

      - rewrite plus_assoc, mult_plus_distr_l.
        apply plus_le_compat.

        + apply plus_le_compat.

          * apply mult_le_compat_r.
            apply NPeano.Nat.max_le_compat_r.
            apply NPeano.Nat.le_max_l.

          * apply mult_le_compat_r.
            rewrite max_assoc.
            apply NPeano.Nat.max_le_compat_r.
            rewrite max_comm.
            trivial.

        + rewrite max_assoc.
          apply NPeano.Nat.max_le_compat_r.
          rewrite max_comm.
          trivial.
      }

- destruct p as [ | | n s p c1' t' c2' v' | c t' v' ]; try tauto.

  + destruct t' as [ | | f lv]; try tauto.
    destruct t as [ | | f' lt]; try tauto.
    destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & _).
    subst c2' lt lv f' v'.
    apply IH_p in H8; clear IH_p.
    simpl in H8.
    etransitivity.

    * eexact H8.

    * clear H8.
      apply le_n_S.
      simpl.
      match goal with
      | |- _ + max ?x _ * _ <= _ => set (a := x)
      end.
      do 3 rewrite mult_succ_r.
      rewrite (plus_n_Sm (#ℐ p + suml (map #ℐ lp))).
      rewrite <- plus_assoc.
      apply plus_le_compat_l.
      set (b := map (fun tv : term * value => value_size (snd tv)) c1').
      set (d := map (fun tv : term * value => value_size (snd tv)) c1).
      set (e := map 𝓢 lp).
      set (g := suml (map #ℐ lp)).
      {transitivity (max a (max (maxl e) (maxl d)) * #ℐ p + max a (max (maxl e) (maxl d))).

      - apply plus_le_compat.

        + apply mult_le_compat_r.
          apply NPeano.Nat.max_le_compat_l.
          apply right_from_activation_or_from_left_path; trivial.

        + apply NPeano.Nat.max_le_compat_l.
          apply right_from_activation_or_from_left_path; trivial.

      - rewrite mult_plus_distr_l.
        rewrite (max_assoc a).
        set (h := max (max a (maxl e)) (maxl d)).
        transitivity (S (h * #ℐ p + h * g + h) + h); try omega.
        apply le_plus_trans.
        apply le_S.
        apply plus_le_compat_r.
        apply le_plus_l. }

  + destruct t' as [ | | f lv]; try tauto.
    destruct t as [ | | f' lt]; try tauto.
    destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & _).
    subst c2 lt lv f' v'.
    apply IH_p in H8.
    clear IH_p.
    simpl (value_size _) in H8.
    etransitivity.

    * eexact H8.

    * clear H8.
      set (a := (cbv_read c
     (fapply f
        (map (term_from_value variable function (constructor:=constructor))
           (map proj_right lp))) v)).
     do 2 rewrite plus_n_Sm.
     rewrite <- plus_assoc.
     apply plus_le_compat_l.
     apply right_from_activation_or_from_left_path in H2; trivial.
     simpl cache_left.
     etransitivity. {
       - apply mult_le_compat.

         + apply NPeano.Nat.max_le_compat.

           * apply le_refl.

           * apply H2.

         + apply le_refl.
     }
     nia.

- destruct t as [ | | f lv]; try tauto.
  destruct H as (_ & lp & t & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & _).
  subst lv v c1 c2.
  simpl.
  etransitivity.

  + apply IH.
    trivial.

  + clear IH.
    set (a := match 𝓢 p with
     | 0 =>
         S
           (suml
              (map (term_size (constructor:=constructor))
                 (map
                    (term_from_value variable function
                       (constructor:=constructor)) (map (psubst s) lp))) +
            value_size (proj_right p))
     | S m' =>
         S
           (max
              (suml
                 (map (term_size (constructor:=constructor))
                    (map
                       (term_from_value variable function
                          (constructor:=constructor)) (map (psubst s) lp))) +
               value_size (proj_right p)) m')
     end).
    set (b := maxl (map (fun tv : term * value => value_size (snd tv)) (cache_left p))).
    rewrite mult_succ_r.
    do 2 rewrite plus_n_Sm.
    apply plus_le_compat_l.
    destruct (𝓢 p) as [ | m].

    * rewrite max_0_l.
      transitivity (max a b * #ℐ p); try omega.
      apply mult_le_compat_r.
      apply NPeano.Nat.le_max_r.

    * transitivity (max a b * #ℐ p); try omega.
      apply mult_le_compat_r.
      apply NPeano.Nat.max_le_compat_r.
      unfold a.
      apply le_n_S.
      apply NPeano.Nat.le_max_r.

- destruct t as [ | | f lv]; try tauto.
  destruct H as [Ht [lv' Hlv']].
  apply assoc_in in Ht.
  + assert (Hin : In (value_size v) (map (fun tv : term * value => value_size (snd tv)) c)) by
      (rewrite in_map_iff; exists (fapply f lv, v); tauto).
    apply maxl_is_max in Hin.
    omega.

  + intros.
    eapply term_beq_eq; eauto.
Qed.

Lemma size_bounded_nb_size_judgements p :
  ∣p∣ <= #ℐ p * max_judgement_size p + cache_size (cache_left p).
Proof.
unfold size.
apply plus_le_compat_r.
induction p as [ lp c1 t c2 v IH_lp | lp p c1 t c2 v IH_lp IH_p | i s p c1 t c2 v IH_p | c t v] using cbv_ind2.

- etransitivity.

  + apply plus_le_compat_l.
    apply suml_map_le in IH_lp.
    apply IH_lp.

  + apply plus_le_compat.

    * apply le_max_l.

    * { etransitivity.

        - apply suml_map_mult_le_suml_mult_maxl.

        - apply mult_le_compat_l.
          apply le_max_r.
      }

- etransitivity.

  + simpl.
    rewrite <- plus_assoc.
    apply plus_le_compat_l.
    apply plus_le_compat.

    * apply IH_p.

    * apply suml_map_le in IH_lp.
      apply IH_lp.

  + apply plus_le_compat.

    * apply le_max_l.

    * fold mult plus nb_judgements.
      { etransitivity.

        - apply plus_le_compat_l.
          apply suml_map_mult_le_suml_mult_maxl.

        - ring_simplify.
          apply plus_le_compat.

          + apply mult_le_compat_l.
            etransitivity; [idtac | apply le_max_r]; apply le_max_l.

          + apply mult_le_compat_l.
            etransitivity; [idtac | apply le_max_r]; apply le_max_r.
      }

- etransitivity.

  + do 2 apply plus_le_compat_r.
    fold size_rec.
    apply IH_p.

  + rewrite <- plus_assoc.
    rewrite plus_comm.
    apply plus_le_compat.

    * apply le_max_l.

    * apply mult_le_compat_l.
      apply le_max_r.

- simpl; omega.
Qed.

(** Proposition 33 *)
Lemma nb_ℐᵖ_bound_gen : forall p p',
  let S := 𝓢 p in
  wf p ->
  In p' (ℐᵃ p) -> #𝓓 p' <= 𝓡 prog S.
Proof.
intros p p' S H_wf_p Hp'.
assert (wf p') as H1. {
  apply ℐᵃ_wf with p.
  exact H_wf_p.
  assumption.
}
generalize Hp'; intro H2p'.
apply activation_is_function in Hp'.
apply le_𝓢 in H2p'.
destruct Hp' as (i' & s' & p'' & c1 & t' & c2 & v' & Hp').
subst p'.
etransitivity.

- apply nb_ℐᵖ_bound.
    assumption.

- simpl in H1.
    destruct t' as [ | | f lv]; try omega.
    destruct H1 as (H1 & lp & t' & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
    subst lv v' c1 c2.
    simpl in H2p'.
    apply 𝓡_monotone.
    etransitivity; [idtac | apply H2p'].
    simpl; omega.
Qed.

(** First part of Proposition 34*)
Lemma nb_judgements_bound_gen : forall i s p' c1 t c2 v,
  let p := cbv_update i s p' c1 t c2 v in
  let A := 𝓐 p in
  let S := 𝓢 p in
  wf p ->
  #ℐ p <= A * 𝓡 prog S + A + (Datatypes.S (max_arity * #ℐᵃ⁺ᵖ p)).
Proof.
intros i s p' c1 t c2 v p A S H_wf_p.
etransitivity.
apply nb_judgements_bound.
unfold A, p.
apply plus_le_compat.

- apply plus_le_compat_r.
  set (list_activ := ℐᵃ (cbv_update i s p' c1 t c2 v)).
  etransitivity.

  + apply suml_le_len_times_bound.
    instantiate (1 := 𝓡 prog S).
    intros x H_x.
    apply in_map_iff in H_x.
    destruct H_x as [ p'' [ H_x1 H_x2 ]].
    subst x.
    apply nb_ℐᵖ_bound_gen; tauto.

  + apply mult_le_compat_r.
    rewrite map_length.
    trivial.

- apply nb_read_bound; trivial.
Qed.

Lemma cache_path_incl : forall lp c1 c2,
  andl (map wf lp) -> cache_path c1 c2 lp = true -> incl c1 c2.
Proof.
  induction lp; intros c1 c2 Hwf path.
  - simpl in path.
    rewrite cache_beq_eq in path.
    subst c1.
    apply incl_refl.

  - simpl in path.
    rewrite andb_true_iff in path.
    rewrite cache_beq_eq in path.
    destruct Hwf as [Hwfa Hwf].
    apply incl_tran with (cache_right a).

    + replace c1 with (cache_left a) by
      (destruct path as [H _]; rewrite H; trivial).

      apply cache_content in Hwfa.
      rewrite Hwfa.
      apply incl_appr.
      apply incl_refl.

    + apply IHlp; tauto.
Qed.

Lemma InCBV_cache_right_incl p π :
  wf π ->
  InCBV p π ->
  incl (cache_right p) (cache_right π).
Proof.
  induction π using cbv_ind2; intros Hwf Hin.
  - destruct Hin as [Heq | Hin].
    + rewrite Heq; apply incl_refl.

    + apply orl_map in Hin.
      destruct Hin as (p0 & Hin0 & Hinpp0).
      simpl in*.
      destruct t; try tauto; destruct v; try tauto.
      destruct Hwf as (path & Hc0 & _ & _ & Hwflp & _).
      apply in_split in Hin0.
      destruct Hin0 as (l1 & l2 & Hl12).
      subst lp.
      rewrite map_app in Hwflp.
      apply andl_app in Hwflp.
      destruct Hwflp as [_ [Hwfp0 Hwf2]].
      apply incl_tran with (cache_right p0).
      * apply H; [auto with* | |]; tauto.

      * apply cache_path_app in path.
        simpl in path.
        rewrite andb_true_iff in path.
        apply cache_path_incl with l2; tauto.

  - destruct Hin as [Heq | [Hinp | Hin]].
    + rewrite Heq; apply incl_refl.

    + simpl.
      apply incl_tran with (cache_right π).
      * apply IHπ.
        simpl in Hwf.
        destruct π; try tauto; destruct t; try tauto; destruct t0; try tauto.
        assumption.

      * simpl in Hwf.  destruct π; try tauto; destruct t; try tauto; destruct t0; try tauto; simpl;
        destruct Hwf as [Hwf _]; subst c2; apply incl_refl.

    + apply orl_map in Hin.
      destruct Hin as (p0 & Hin0 & Hinpp0).
      specialize (H p0 Hin0).
      apply in_split in Hin0.
      destruct Hin0 as (l1 & l2 & Hl12).
      subst lp.
      destruct π; try tauto; destruct t; try tauto; destruct t0; simpl in Hwf;try tauto; simpl in *;
       (decompose record Hwf;
        rewrite map_app, andl_app in H4;
        simpl in H4;
        destruct H4 as (_ & Hwfp0 & Hwfl2);
        specialize (H Hwfp0 Hinpp0);
        apply (incl_tran H);
        apply cache_path_app in H2;
        simpl in H2;
        rewrite andb_true_iff in H2;
        decompose record H2);
          [apply incl_tran with (cache_right π); [| subst c0; subst c2; auto with *];
          apply incl_tran with (cache_left π); [| rewrite cache_content; auto with *] |];
        subst c;
        apply cache_path_incl with l2; assumption.

 - destruct Hin as [Heq | Hin].
    + rewrite Heq; apply incl_refl.

    + simpl in *.
      destruct t; try tauto.
      destruct Hwf as (_ & lp & t & Hw).
      apply incl_tran with (cache_right π).
      * apply IHπ; tauto.

      * replace c2 with ((fapply f l, v) :: cache_right π) by
          (decompose record Hw; apply eq_sym; assumption).
        auto with *.

 - destruct Hin; [subst p; apply incl_refl | tauto].
Qed.

Lemma InCBV_read_cache_right c t v p:
  wf p ->
  InCBV (cbv_read c t v) p ->
  In (t, v) (cache_right p).
Proof.
  intros Hwf Hin.
  assert(Hwf' : wf (cbv_read c t v)) by
   (apply wf_InCBV_wf with p; trivial).
  simpl in Hwf'.
  destruct t; try tauto.
  destruct Hwf' as (Hinc & _).
  apply assoc_in in Hinc; [ | apply term_beq_eq; trivial].
  assert (incl c (cache_right p)).
  * replace c with (cache_right (cbv_read c (fapply f l) v)) by trivial.
    apply (InCBV_cache_right_incl Hwf); trivial.

  * apply H; assumption.
Qed.

Lemma term_size_proj_left_bound : forall i s p' c1 t c2 v,
  let p := cbv_update i s p' c1 t c2 v in
  let S := 𝓢 p in
  wf p ->
  forall p',
  InCBV p' p -> ╎proj_left p'╎ <= 𝓡 prog S + S + cache_size c1.
Proof.
(** We use cbv_reverse_induction to prove ≤ activation S + S
   - base case: it is a cbv_function, thus bounded by S
   - cas inductifs :
     - the sub-tree of a cbv_function is bounded by act S,
     - the sub-trees of a cbv_constr are bounded by the cbv_constr itself,
     -  cbv_split:
       - the sub-trees in lp are bounded by the cbv_split itself,
       - the sub-tree p is a cbv_function, thus bounded by S *)

intros i s p0 c1 t c2 v p S H_wf_p.
apply cbv_reverse_induction.

- (* base case *)
  transitivity S.

  + unfold p, S.
    simpl.
    transitivity (╎t╎ + value_size v).

    * apply le_plus_l.

    * apply le_max_l.

  + omega.

- (* cbv_constr *)
  intros lp c1' t' c2' v' H_p'_in_p IH p'' H_p''_in_lp.
  transitivity (╎proj_left (cbv_constr lp c1' t' c2' v')╎).

  + generalize (wf_InCBV_wf H_wf_p H_p'_in_p).
    simpl.
    destruct t' as [ | c lt | ]; try tauto.
    destruct v' as [c' lv ].
    intros (_ & H_c0 & H_l_lt & _ & H_wf_lp & _).
    subst c' lt.
    simpl.
    apply le_S.
    apply in_le_suml.
    apply in_map.
    apply in_map.
    apply H_p''_in_lp.

  + exact IH.

- (* cbv_split *)
  intros lp p' c1' t' c2' v' H_in_p IH p'' [ H_p''_in | H_p''_in ].

  + (* p'' = p' *)
    subst p''. simpl.
    transitivity (S + cache_size c1).
      (* apply le_𝓢. *)
      generalize (wf_InCBV_wf H_wf_p H_in_p).
      intro H_wf_split.
      simpl in H_wf_split.
      {destruct p' as [ | | i' s' p' c1'' t'' c2'' v'' | c t'' v'' ]; try tauto.

      - (* cbv_update *)

        transitivity (╎proj_left (cbv_update i' s' p' c1'' t'' c2'' v'')╎ +
                       value_size (proj_right (cbv_update i' s' p' c1'' t'' c2'' v''))).
        + apply le_plus_l.

        + transitivity S.
          * apply le_𝓢.
            eapply cbv_update_in_ℐᵃ_InCBV; try reflexivity.
            apply InCBV_trans with (cbv_split lp (cbv_update i' s' p' c1'' t'' c2'' v'') c1' t' c2' v'); trivial.
            simpl; tauto.

          * apply le_plus_l.

      - (* cbv_read *)
        destruct t''; try tauto; destruct t'; try tauto.
        replace c2 with (cache_right (cbv_update i s p0 c1 t c2 v)) in *; trivial.
        assert(In (fapply f l, v') (cache_right (cbv_update i s p0 c1 t c2 v))).
        + apply InCBV_read_cache_right with c.
          * assumption.

          * simpl in H_in_p.
            simpl.
            right.
            decompose record H_wf_split.
            subst v''.
            destruct H_in_p as [Heq | Hneq]; [inversion Heq | ].
            simpl in Hneq.
            apply InCBV_trans with (cbv_split lp (cbv_read c (fapply f l) v') c1' (fapply f0 l0) c2' v');
            simpl; tauto.

        + rewrite cache_content in H; [| assumption].
          apply in_app_or in H.
          destruct H as [Hleft | Hright].
          * transitivity S; [|omega].
            apply in_map_iff in Hleft.
            destruct Hleft as (x & Hcache & Hact).
            simpl proj_left.
            unfold cbv_cache_entry in Hcache.
            replace (fapply f l) with (proj_left x) by (inversion Hcache; trivial).
            transitivity (╎proj_left x╎ + value_size(proj_right x)); [omega|].
            apply le_𝓢.
            eapply Permutation_in.
            apply Permutation_sym.
            apply ℐᵃ_cache_order_are_ℐᵃ.
            assumption.

          * simpl in Hright.
            transitivity (cache_size c1); [|omega].
            unfold cache_size.
            simpl proj_left.
            transitivity (╎fst (fapply f l, v')╎ + value_size (snd (fapply f l, v'))); [auto with*|].
            apply in_le_suml.
            apply in_map_iff.
            eauto.
}

    * omega.

  + (* p'' ∈ lp, similar to the cbv_constr case *)
    transitivity (╎proj_left (cbv_split lp p' c1' t' c2' v')╎).

    * generalize (wf_InCBV_wf H_wf_p H_in_p).
      simpl.
      {destruct p' as [ | | i' s' p' c1'' t'' c2'' v'' | c t'' v'' ]; try tauto.

      + (* cbv_update *)
        destruct t'' as [ | | f lv ]; try tauto.
        destruct t' as [ | | f' lt ]; try tauto.
        intros (_ & _ & H_lt_lp & _ & _ & H_f & H_v & _).
        subst f' v'' lt.
        simpl.
        apply le_S.
        apply in_le_suml.
        apply in_map.
        apply in_map.
        assumption.

      + (* cbv_read *)
        destruct t'' as [ | | f lv ]; try tauto.
        destruct t' as [ | | f' lt ]; try tauto.
        intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
        subst c2' lt lv f' v''.
        simpl.
        rewrite map_map.
        apply le_S, in_le_suml.
        rewrite in_map_iff.
        eauto. }

    * assumption.

- (* cbv_update *)
  intros i' s' p' c1' t' c2' v' H_in_p IH.
  transitivity (𝓡 prog (╎t'╎)).

  + change t' with (proj_left (cbv_update i' s' p' c1' t' c2' v')).
    replace (proj_left p') with (subst s' (rhs_of_rule (nth i' prog rule_default))).

    * generalize (@𝓡_spec s p H_wf_p (cbv_update i' s' p' c1' t' c2' v')).
      simpl.
      intro H.
      apply H.
      simpl in H_in_p.
      {
        destruct H_in_p as [ H_in_p | H_in_p ].

        - left.
          symmetry.
          assumption.

        - right.
          apply (@cbv_update_in_ℐᵃ_InCBV p0 (cbv_update i' s' p' c1' t' c2' v') i' s' p' c1' t' c2' v'); trivial.
      }

    * generalize (wf_InCBV_wf H_wf_p H_in_p).
      simpl.
      destruct t' as [ | | f lv ]; try tauto.
      intros (_ & lp & t' & _ & H_nth_rule & _ & H_proj_subst & _).
      rewrite H_proj_subst.
      f_equal.
      rewrite H_nth_rule.
      simpl.
      trivial.

  + apply le_plus_trans.
    transitivity(𝓡 prog S); try omega.
    apply 𝓡_monotone.
    transitivity (╎proj_left (cbv_update i' s' p' c1' t' c2' v')╎ + value_size (proj_right (cbv_update i' s' p' c1' t' c2' v'))).

    * apply le_plus_trans.
      simpl.
      trivial.

    * apply le_𝓢.
      apply cbv_update_in_ℐᵃ_InCBV with i' s' p' c1' t' c2' v'; trivial.
Qed.

(** Last line of Proposition 34. *)
Lemma nb_nodes_bound_gen i s p' c1 t c2 v :
  let p := cbv_update i s p' c1 t c2 v in
  let A := 𝓐 p in
  let S := 𝓢 p in
  wf p ->
  #ℐᵃ⁺ᵖ p <= A * (1 + 𝓡 prog S).
Proof.
intros p A S H_wf_p.
etransitivity.
apply nb_nodes_bound.
rewrite mult_plus_distr_l, mult_1_r, plus_comm.
apply plus_le_compat_l.
fold p.
etransitivity. {
  apply suml_map_le.
  intros p'' Hp''.
  apply nb_ℐᵖ_bound_gen with (p := p).
  exact H_wf_p.
  tauto.
}
fold S.
rewrite suml_map_const, mult_comm.
trivial.
Qed.

Lemma size_judgement : forall i s p' c1 t c2 v,
  let p := cbv_update i s p' c1 t c2 v in
  let A := 𝓐 p in
  let S := 𝓢 p in
  let C := maxl (map (fun tv : term * value => value_size (snd tv)) c1) in
  wf p ->
  max_judgement_size p <=
  𝓡 prog S + S + cache_size c1 +
  (1 + max S C) * (1 + (A * 𝓡 prog S + A) + max_arity * (A * 𝓡 prog S + A)).
Proof.
intros i s p0 c1 t c2 v p A S C H_wf_p. unfold 𝓐 in A.
etransitivity. {
  apply judgement_size_le_projs_size. }
  apply plus_le_compat.

-  apply term_size_proj_left_bound; trivial.
  apply InCBV_proj_left_max_size.

- transitivity ((1 + max S C) * #ℐ p).

  + clear A.
    subst C.
    change c1 with (cache_left p).
    induction p as [ lp c1' t' c2' v' IH | lp p' c1' t' c2' v' IH_lp IH_p' | i' s' p' c1' t' c2' v' IH | c t' v' ] using cbv_ind2;
     subst S; simpl.

    * {apply max_lub.

      - change v' with (proj_right (cbv_constr lp c1' t' c2' v')).
        etransitivity. {
          apply value_size_bounded_by_nb_judgements; trivial.
        }
        trivial.

      - apply all_max_le.
        intros n Hn.
        rewrite in_map_iff in Hn.
        destruct Hn as (p & H1 & H2).
        subst n.
        etransitivity. {
          apply IH; trivial.
          eapply wf_InCBV_wf.

          - eexact H_wf_p.

          - simpl.
            right.
            apply orl_map.
            exists p.
            split; trivial.
            apply InCBV_refl.
        }
        clear IH.
        apply in_split in H2.
        destruct H2 as (lp1 & lp2 & H2).
        subst lp.
        transitivity (
          #ℐ p +
          max (𝓢 p) (maxl (map (fun tv : term * value => value_size (snd tv)) (cache_left p))) *
          #ℐ p
        ); trivial.
        apply le_S.
        apply plus_le_compat.

        + apply in_le_suml.
          rewrite in_map_iff.
          exists p.
          split; trivial.
          apply in_or_app.
          simpl; tauto.

        + apply mult_le_compat.

          * { apply max_lub.
            - etransitivity; [ idtac | apply le_max_l ].
              apply maxl_is_max.
              rewrite in_map_iff.
              exists p.
              split; trivial.
              apply in_or_app.
              simpl; tauto.

            - simpl in H_wf_p.
              destruct t' as [ | c lt | ]; try tauto.
              destruct v' as [ c' lv ].
              destruct H_wf_p as (H1 & _ & _ & _ & H2 & _).
              etransitivity. {
                apply right_from_activation_or_from_left_path.

                - rewrite map_app, andl_app in H2.
                  destruct H2 as [ H2 _ ].
                  eexact H2.

                - apply cache_path_app in H1.
                  destruct H1 as [ H1 _ ].
                  eexact H1.
              }
              apply max_lub; [ idtac | lia ].
              etransitivity; [ idtac | apply le_max_l ].
              rewrite map_app, maxl_app.
              lia. }

          * apply le_S.
            apply in_le_suml.
            rewrite in_map_iff.
            exists p.
            split; trivial.
            apply in_or_app.
            simpl; tauto. }

    * {apply max_lub.

      - change v' with (proj_right (cbv_split lp p' c1' t' c2' v')).
        etransitivity. {
          apply value_size_bounded_by_nb_judgements; trivial.
        }
        trivial.

      - apply max_lub. {
          clear IH_lp.
          etransitivity. {
            apply IH_p'.
            eapply wf_InCBV_wf.

            - eexact H_wf_p.

            - simpl.
              right; left.
              apply InCBV_refl.
          }
          clear IH_p'.
          simpl in H_wf_p.
          destruct p' as [ | | i' s' p' c1'' t'' c2'' v'' | c t'' v'' ]; try tauto; simpl.

          + destruct t'' as [ | | f lv ]; try tauto.
            destruct t' as [ | | f' lt ]; try tauto.
            destruct H_wf_p as (H1 & H2 & _ & _ & H3 & H4 & H5 & H6 & _).
            subst c2'' f' v''.
            apply le_n_S.
            apply le_S.
            rewrite <- plus_assoc.
            apply plus_le_compat_l.
            rewrite (plus_comm (suml _)).
            apply le_plus_trans.
            apply mult_le_compat; [ idtac | omega ].
            apply max_lub; [ lia | idtac ].
            etransitivity. {
              apply right_from_activation_or_from_left_path.

              - eexact H3.

              - eexact H2.
            }
            lia.

          + destruct t'' as [ | | f lv ]; try tauto.
            destruct t' as [ | | f' lt ]; try tauto.
            destruct H_wf_p as (H1 & H2 & _ & _ & H3 & H4 & H5 & H6 & _).
            subst c2' f' v''.
            apply le_n_S.
            apply le_S.
            rewrite (plus_comm (suml _)).
            apply le_plus_trans.
            apply mult_le_compat; [ idtac | omega ].
(*            apply max_lub; [ lia | idtac ]. *)
            etransitivity. {
              apply right_from_activation_or_from_left_path.

              - eexact H3.

              - eexact H2.
            }
            lia.
        }
        clear IH_p'.
        apply all_max_le.
        intros n Hn.
        rewrite in_map_iff in Hn.
        destruct Hn as (p & H1 & H2).
        subst n.
        etransitivity. {
          apply IH_lp; trivial.
          eapply wf_InCBV_wf.

          - eexact H_wf_p.

          - simpl.
            right; right.
            apply orl_map.
            exists p.
            split; trivial.
            apply InCBV_refl.
        }
        clear IH_lp.
        apply in_split in H2.
        destruct H2 as (lp1 & lp2 & H2).
        subst lp.
        transitivity (
          #ℐ p +
          max (𝓢 p) (maxl (map (fun tv : term * value => value_size (snd tv)) (cache_left p))) *
          #ℐ p
        ); trivial.
        apply le_S.
        rewrite <- plus_assoc, (plus_comm (#ℐ p')).
        apply le_plus_trans.
        apply plus_le_compat.

        + apply in_le_suml.
          rewrite in_map_iff.
          exists p.
          split; trivial.
          apply in_or_app.
          simpl; tauto.

        + apply mult_le_compat.

          * { apply max_lub.
            - etransitivity; [ idtac | apply le_max_l ].
              etransitivity; [ idtac | apply le_max_r ].
              apply maxl_is_max.
              rewrite in_map_iff.
              exists p.
              split; trivial.
              apply in_or_app.
              simpl; tauto.

            - simpl in H_wf_p.
              destruct p' as [ | | i' s' p' c1'' t'' c2'' v'' | c t'' v'' ]; try tauto.

              + destruct t'' as [ | | f lv ]; try tauto.
                destruct t' as [ | | f' lt ]; try tauto.
                destruct H_wf_p as (H1 & H2 & _ & _ & H3 & H4 & H5 & H6 & _).
                subst c2'' f' v''.
                etransitivity. {
                  apply right_from_activation_or_from_left_path.

                  - rewrite map_app, andl_app in H3.
                    destruct H3 as [ H3 _ ].
                    eexact H3.

                  - apply cache_path_app in H2.
                    destruct H2 as [ H2 _ ].
                    eexact H2.
                }
                apply max_lub; [ idtac | lia ].
                etransitivity; [ idtac | apply le_max_l ].
                rewrite map_app, maxl_app.
                lia.

              + destruct t'' as [ | | f lv ]; try tauto.
                destruct t' as [ | | f' lt ]; try tauto.
                destruct H_wf_p as (H1 & H2 & _ & _ & H3 & H4 & H5 & H6 & _).
                subst c2' f' v''.
                etransitivity. {
                  apply right_from_activation_or_from_left_path.

                  - rewrite map_app, andl_app in H3.
                    destruct H3 as [ H3 _ ].
                    eexact H3.

                  - apply cache_path_app in H2.
                    destruct H2 as [ H2 _ ].
                    eexact H2.
                }
                apply max_lub; [ idtac | lia ].
                etransitivity; [ idtac | apply le_max_l ].
                rewrite map_app, maxl_app.
                lia. }

          * apply le_S.
            rewrite plus_comm.
            apply le_plus_trans, in_le_suml.
            rewrite in_map_iff.
            exists p.
            split; trivial.
            apply in_or_app.
            simpl; tauto. }

    * {apply max_lub.

      - change v' with (proj_right (cbv_update i' s' p' c1' t' c2' v')).
        etransitivity. {
          apply value_size_bounded_by_nb_judgements; trivial.
        }
        trivial.

      - etransitivity. {
          apply IH.
          eapply wf_cbv_update.
          eexact H_wf_p.
        }
        clear IH.
        simpl.
        rewrite plus_n_Sm.
        apply plus_le_compat_l.
        simpl in H_wf_p.
        destruct t' as [ | | f lv ]; try tauto.
        destruct H_wf_p as (H1 & lp & t' & H2 & H3 & H4 & H5 & H7 & H8 & H9 & H10 & H11 & H12).
        subst lv v' c1' c2'.
        nia. }

    * simpl in H_wf_p.
      destruct t'; try tauto.
      destruct H_wf_p as [Hassoc _].
      apply assoc_in in Hassoc; try apply term_beq_eq; trivial.
      rewrite mult_1_r.
      apply le_S.
      apply maxl_is_max.
      apply in_map_iff.
      exists (fapply f l, v').
      tauto.

  + apply mult_le_compat_l.
    etransitivity. {
      apply nb_judgements_bound_gen; trivial. }
    simpl.
    assert (𝓡 prog (max (╎t╎ + value_size v) (𝓢 p0)) <= 𝓡 prog S) as H. {
      apply 𝓡_monotone; trivial. }
    etransitivity. {
      do 2 apply plus_le_compat_r.
      apply plus_le_compat.

      - eexact H.

      - apply mult_le_compat_l.
        eexact H. }
    clear H.
    rewrite plus_n_Sm.
    repeat rewrite <- plus_assoc.
    do 2 apply plus_le_compat_l.
    apply plus_le_compat; trivial.
    apply le_n_S.
    apply mult_le_compat_l.
    transitivity (#ℐᵃ⁺ᵖ p); trivial.
    replace (length (ℐᵃ p0)) with (A - 1); try (simpl; omega).
    rewrite plus_assoc, mult_minus_distr_r, mult_1_l.
    transitivity (A * (1 + 𝓡 prog S)); try lia.
    apply nb_nodes_bound_gen.
    exact H_wf_p.
Qed.

Theorem size_bound_gen : forall i s p' c1 t c2 v,
  let p := cbv_update i s p' c1 t c2 v in
  let A := 𝓐 p in
  let S := 𝓢 p in
  wf p ->
  ∣p∣ <=
  (A * 𝓡 prog S + A + 1 + (max_arity * A * (1 + 𝓡 prog S))) *
  (𝓡 prog S + S + cache_size c1 +
  (1 + max S (maxl (map (fun tv : term * value => value_size (snd tv)) c1))) *
  (1 + (A * 𝓡 prog S + A) + max_arity * (A * 𝓡 prog S + A))) +
  cache_size c1.
Proof.
intros i s p0 c1 t c2 v p A S H_wf_p.
etransitivity. {
  apply size_bounded_nb_size_judgements.
}
apply plus_le_compat_r.
apply mult_le_compat.

- etransitivity. {
    apply nb_judgements_bound_gen; trivial.
  }
  fold p A S.
  rewrite <- (plus_assoc _ 1).
  apply plus_le_compat_l, le_n_S.
  rewrite <- mult_assoc.
  apply mult_le_compat_l.
  apply nb_nodes_bound_gen; trivial.

- apply size_judgement; trivial.
Qed.

(* This corollary corresponds to Proposition 6. *)
Corollary size_bound : forall i s p' t c v,
  let p := cbv_update i s p' [] t c v in
  let A := 𝓐 p in
  let S := 𝓢 p in
  wf p ->
 ∣p∣ <=
  (A * 𝓡 prog S + A + 1 + (max_arity * A * (1 + 𝓡 prog S))) *
  (𝓡 prog S + S +
  (1 + S) *
  (1 + (A * 𝓡 prog S + A) + max_arity * (A * 𝓡 prog S + A))).
Proof.
intros i s p0 t c v p A S H_wf_p.
etransitivity. {
  apply size_bound_gen; trivial.
}
unfold cache_size.
simpl.
do 2 rewrite plus_0_r.
apply mult_le_compat; trivial.
apply plus_le_compat; trivial.

apply le_n_S.
apply plus_le_compat; trivial.
rewrite max_0_r; trivial.
Qed.

End CBV.
