(** * Call by value semantics **)
Require Import Arith Compare_dec Max List Omega.
Import List.ListNotations.
Require Import Cecoa.Lib Cecoa.Syntax.

Set Implicit Arguments.
Unset Strict Implicit.

Section CBV.

Variables variable function constructor : Type.
Variable max_arity : nat.

Notation value := (Syntax.value constructor).
Notation term := (Syntax.term variable function constructor).
Notation pattern := (Syntax.pattern variable constructor).
Notation rule := (Syntax.rule variable function constructor).
Notation "'╎' t '╎'" := (@term_size variable function constructor t) (at level 10).

(** Definition of a proof tree *)

Inductive cbv : Type :=
| cbv_constr : list cbv -> term -> value -> cbv
| cbv_split : list cbv -> cbv -> term -> value -> cbv
| cbv_function : nat -> (variable -> value) -> cbv -> term -> value -> cbv.

(** Smarter induction principle than the one automatically generated *)

Lemma cbv_ind2_gen :
  forall (P : cbv -> Set)(Q : list cbv -> Set),
  Q nil ->
  (forall p lp, P p -> Q lp -> Q (p :: lp)) ->
  (forall lp t v, Q lp -> P (cbv_constr lp t v)) ->
  (forall lp p t v, Q lp -> P p -> P (cbv_split lp p t v)) ->
  (forall n s p t v, P p -> P (cbv_function n s p t v)) ->
  forall p, P p.
Proof.
fix H1 8; intros P Q H2 H3 H4 H5 H6 [ lp t v | lp p t v | n s p t v ].

- apply H4; revert lp; fix H7 1; intros [ | p lp].

  + exact H2.

  + apply H3.

    * { apply H1 with (Q:=Q).

      - exact H2.

      - exact H3.

      - exact H4.

      - exact H5.

      - exact H6. }

    * apply H7.

- apply H5; revert lp; fix H7 1; intros [ | p' lp].

  + exact H2.

  + apply  H3.

    * { apply H1 with (Q:=Q).

      - exact H2.

      - exact H3.

      - exact H4.

      - exact H5.

      - exact H6. }

    * apply H7.

  + apply H1 with (Q:=Q).

    * exact H2.

    * exact H3.

    * exact H4.

    * exact H5.

    * exact H6.

  + apply H1 with (Q:=Q).

    * exact H2.

    * exact H3.

    * exact H4.

    * exact H5.

    * exact H6.

- apply H6.
  apply H1 with (Q:=Q).

  + exact H2.

  + exact H3.

  + exact H4.

  + exact H5.

  + exact H6.

Qed.

Lemma cbv_ind2 :
  forall (P : cbv -> Prop),
  (forall lp t v, (forall p, In p lp -> P p) -> P (cbv_constr lp t v)) ->
  (forall lp p t v, (forall p, In p lp -> P p) -> P p -> P (cbv_split lp p t v)) ->
  (forall n s p t v, P p -> P (cbv_function n s p t v)) ->
  forall p, P p.
Proof.
intros P H1 H2 H3 p.
apply cbv_ind2_gen with (Q := fun lp => forall p, In p lp -> P p); simpl; try tauto.
intuition; subst; trivial.
Qed.

(** Being a subtree of *)

Fixpoint InCBV p π : Prop :=
  p = π \/
  match π with
      | cbv_constr lp _ _ => orl (map (InCBV p) lp)
      | cbv_split lp p' _ _ => InCBV p p' \/ orl (map (InCBV p) lp)
      | cbv_function _ _ p' _ _ => InCBV p p'
  end.

Lemma InCBV_refl p : InCBV p p.
Proof.
induction p as [lp t v IH_lp | lp p t v IH_lp IH_p | i s p t v IH_p] using cbv_ind2;
simpl; tauto.
Qed.

Lemma InCBV_trans p p' p'': InCBV p p' -> InCBV p' p'' -> InCBV p p''.
Proof.
revert p p'.
induction p'' as [lp t v IH_lp | lp p1 t v IH_lp IH_p' | i s p1 t v IH_p'] using cbv_ind2;
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
Qed.

(** Reverse induction on proof trees *)

Lemma cbv_reverse_induction :
  forall (P : cbv -> Prop) π,
  P π ->
  (forall lp t v, InCBV (cbv_constr lp t v) π -> P (cbv_constr lp t v) -> forall p, In p lp -> P p) ->
  (forall lp p t v, InCBV (cbv_split lp p t v) π -> P (cbv_split lp p t v) -> forall p', (p' = p \/ In p' lp) -> P p') ->
  (forall i s p t v, InCBV (cbv_function i s p t v) π -> P (cbv_function i s p t v) -> P p) ->
  forall p, InCBV p π -> P p.
Proof.
intros P π H_π H_constr H_split H_function p H_p.
induction π as [lp t v IH_lp | lp p' t v IH_lp IH_p' | i s p' t v IH_p'] using cbv_ind2;
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

    * intros lp' t' v' H3 H4 p'' H5.
      apply H_constr with lp' t' v'; trivial.
      simpl.
      right.
      apply orl_map.
      exists p'.
      tauto.

    * intros lp' p'' t' v' H3 H4 p''' H5.
      apply H_split with lp' p'' t' v'; trivial.
      simpl.
      right.
      apply orl_map.
      exists p'.
      tauto.

    * intros i s p'' t' v' H3 H4.
      apply H_function with i s t' v'; trivial.
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

    * intros lp' t' v' H3 H4 p'' H5.
      apply H_constr with lp' t' v'; trivial.
      simpl; tauto.

    * intros lp' p'' t' v' H3 H4 p''' H5.
      apply H_split with lp' p'' t' v'; trivial.
      simpl; tauto.

    * intros i s p'' t' v' H3 H4.
      apply H_function with i s t' v'; trivial.
      simpl; tauto.

    * exact H_p.

  + apply orl_map in H_p.
    destruct H_p as [p'' [H1 H2] ].
    apply IH_lp with p''; trivial.
    eapply H_split.

    * apply InCBV_refl.

    * exact H_π.

    *  right; exact H1.

    * intros lp' t' v' H3 H4 p''' H5.
      apply H_constr with lp' t' v'; trivial.
      simpl.
      right; right.
      apply orl_map.
      exists p''.
      tauto.

    * intros lp' p''' t' v' H3 H4 p'''' H5.
      apply H_split with lp' p''' t' v'; trivial.
      simpl.
      right; right.
      apply orl_map.
      exists p''.
      tauto.

    * intros i s p''' t' v' H3 H4.
      apply H_function with i s t' v'; trivial.
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

    * intros lp' t' v' H3 H4 p'' H5.
      apply H_constr with lp' t' v'; trivial.
      simpl; tauto.

    * intros lp' p'' t' v' H3 H4 p''' H5.
      apply H_split with lp' p'' t' v'; trivial.
      simpl; tauto.

    * intros i' s' p'' t' v' H3 H4.
      apply H_function with i' s' t' v'; trivial.
      simpl; tauto.

    * exact H_p.
Qed.

Variable subst_default : variable -> value.

Definition rule_subst_of_cbv_function (π : cbv) : nat * (variable -> value) :=
  match π with
  | cbv_function i s _ _ _ => (i, s)
  | _ => (0, subst_default) (* impossible case *)
  end.

(** Term of a tree *)
Definition proj_left (π : cbv) : term :=
  match π with
    | cbv_constr _ t _ => t
    | cbv_split _ _ t _ => t
    | cbv_function _ _ _ t _ => t
  end.

(** value of a tree *)
Definition proj_right (π : cbv) : value :=
  match π with
    | cbv_constr _ _ v => v
    | cbv_split _ _ _ v => v
    | cbv_function _ _ _ _ v => v
  end.

Variable prog : list rule.

Variable rule_default : rule.

(** Well-founded trees *)
Fixpoint wf (π : cbv) : Prop :=
  match π with
    | cbv_constr l (capply c lt) (c_capply c' lv) =>
        c = c' /\
        lt = map proj_left l /\ lv = map proj_right l /\ (* Permutations would also be acceptable *)
        andl (map wf l)
    | cbv_split l ((cbv_function _ _ _ (fapply f lv) v) as p) (fapply f' lt) v' =>
        lt = map proj_left l /\ lv = map (@term_from_value _ _ _)(map proj_right l) /\
        andl (map wf l) /\
        f = f' /\ v = v' /\
        wf p
    | cbv_function i s p (fapply f lv) v =>
        exists lp t,
        i < length prog /\
        nth i prog rule_default = rule_intro f lp t /\
        lv = map (@term_from_value _ _ _) (map (psubst s) lp) /\
        proj_left p = subst s t /\ proj_right p = v /\
        wf p
    | _ => False
  end.

Lemma wf_cbv_function i s p t v : wf (cbv_function i s p t v) -> wf p.
Proof.
destruct t; simpl; try tauto.
intros (lp & t & H); tauto.
Qed.

Lemma wf_InCBV_wf p π: wf π -> InCBV p π -> wf p.
Proof.
intro H_π_wf.
apply cbv_reverse_induction.

- apply H_π_wf.

- intros lp t v _.
  simpl.
  destruct t; try (intro H_false; destruct H_false).
  destruct v.
  intros [ _ [ _ [ _ H_map_wf ] ] ] p' H_in_p'_lp.
  apply andl_in with (map wf lp).

  + apply H_map_wf.

  + apply in_map.
    apply H_in_p'_lp.

- intros lp p' t v _.
  simpl.
  destruct p'; try (intro H_false; destruct H_false).
  destruct t0; try (intro H_false; destruct H_false).
  destruct t; try (intro H_false; destruct H_false).
  generalize H0.
  clear.
  intros [ _ [ H_wf_lp [ _ [ _ H_wf_p' ] ] ] ] p'' H_p''.
  destruct H_p'' as [ H_p'' | H_p'' ].

  + (* case p'' = p' *)
    rewrite H_p''.
    apply H_wf_p'.

  + (* case p'' in lp *)
    apply andl_in with (map wf lp).

    * apply H_wf_lp.

    * apply in_map.
      apply H_p''.

- intros i s p' t v _.
  simpl.
  destruct t; try (intro H_false; destruct H_false).
  generalize H.
  clear.
  intros [ _ [ _ [ _ [ _ [ _ [ _ H_wf ] ] ] ] ] ].
  apply H_wf.
Qed.

(** Sizes *)

Fixpoint size (π : cbv) : nat :=
  match π with
  | cbv_constr l t v => ╎t╎ + value_size v + suml (map size l)
  | cbv_split l p t v => ╎t╎ + value_size v + size p + suml (map size l)
  | cbv_function _ _ p t v => size p + ╎t╎ + value_size v
  end.

Fixpoint max_active_size (π : cbv) : nat :=
  match π with
  | cbv_constr lp _ _ => maxl (map max_active_size lp)
  | cbv_split lp p _ _ => max (max_active_size p) (maxl (map max_active_size lp))
  | cbv_function _ _ p t v => max (╎t╎ + value_size v) (max_active_size p)
  end.

Fixpoint max_judgement_size (π : cbv) : nat :=
  match π with
  | cbv_constr lp t v => max (╎t╎ + value_size v) (maxl (map max_judgement_size lp))
  | cbv_split lp p t v => max (╎t╎ + value_size v) (max (max_judgement_size p) (maxl (map max_judgement_size lp)))
  | cbv_function _ _ p t v => max (╎t╎ + value_size v) (max_judgement_size p)
  end.

(** Judgments (sub-trees) *)

Fixpoint ℐ (π : cbv) : list cbv :=
  π :: (
    match π with
    | cbv_constr lp _ _ => flat_map ℐ lp
    | cbv_split lp p _ _ => flat_map ℐ (p :: lp)
    | cbv_function _ _ p _ _ => ℐ p
    end ).

Lemma ℐ_neq_nil : forall p, ℐ p <> [].
Proof.
destruct p; simpl; congruence.
Qed.

Lemma InCBV_In_ℐ p p' : InCBV p p' <-> In p (ℐ p').
Proof.
split.

- induction p' as [ lp t v IH_lp | lp p' t v IH_lp IH_p | i s p' t v IH_p ] using cbv_ind2; simpl.

  + intros [H1 | H1].

    * left.
      congruence.

    * right.
      rewrite in_flat_map.
      rewrite orl_map in H1.
      firstorder.

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
      firstorder.

  + intros [H1 | H1].

    * left.
      congruence.

    * right.
      apply IH_p.
      exact H1.

- induction p' as [ lp t v IH_lp | lp p' t v IH_lp IH_p | i s p' t v IH_p ] using cbv_ind2;
  simpl; (intros [H1 | H1]; [left; congruence | right] ).

  + rewrite orl_map.
    rewrite in_flat_map in H1.
    firstorder.

  + rewrite in_app_iff in H1.
    destruct H1 as [H1 | H1]; [left; tauto | right].
    rewrite orl_map.
    rewrite in_flat_map in H1.
    firstorder.

  + tauto.
Qed.

(** Returns the proof tree of the list with the largest proj_left *)
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
  | cbv_constr lp t v => max (value_size v) (maxl (map max_proj_right_size lp))
  | cbv_split lp p t v => max (value_size v) (max (max_proj_right_size p) (maxl (map max_proj_right_size lp)))
  | cbv_function _ _ p t v => max (value_size v) (max_proj_right_size p)
  end.

Lemma judgement_size_le_projs_size p :
  max_judgement_size p <= ╎proj_left (proj_left_max_size p)╎ + max_proj_right_size p.
Proof.
induction p as [ lp t v IH_lp | lp p t v IH_lp IH_p | i s p t v IH_p ] using cbv_ind2; simpl.

- destruct (max_dec (╎t╎ + value_size v) (maxl (map max_judgement_size lp))) as [ H | H ];
  rewrite H.

  + apply plus_le_compat.

    * change t with (proj_left (cbv_constr lp t v)) at 1.
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

    * change t with (proj_left ((cbv_split lp p t v))) at 1.
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

    * change t with (proj_left ((cbv_function i s p t v))) at 1.
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

Qed.

(** Activations (ℐᵃ) *)
Fixpoint ℐᵃ (π : cbv) : list cbv :=
  match π with
  | cbv_constr lp _ _ => flat_map ℐᵃ lp
  | cbv_split lp p _ _ => ℐᵃ p ++ flat_map ℐᵃ lp
  | cbv_function _ _ p _ _ as p' => p' :: ℐᵃ p
  end.

Lemma activation_is_function :
  forall π p,
  In p (ℐᵃ π) -> exists i s p' t v, p = cbv_function i s p' t v.
Proof.
intros π p H.
induction π as [ lp t v IH | lp p' t v IH_lp IH_p' | i s p' t v IH ] using cbv_ind2.

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

- (* cbv_function *)
  simpl in H.
  destruct H as [ H_base | H_ind ].

  + repeat eexists.
    symmetry.
    apply H_base.

  + generalize (IH H_ind).
    trivial.
Qed.

Lemma cbv_function_in_ℐᵃ_InCBV π sub_proof_tree i s p t v:
  sub_proof_tree = cbv_function i s p t v ->
  InCBV sub_proof_tree π ->
  In sub_proof_tree (ℐᵃ π).
Proof.
intros H0 H1.
subst.
induction π as [ lp t' v' IH | lp p' t' v' IH1 IH2 | i' s' p' t' v' IH ] using cbv_ind2; simpl in *.

- destruct H1 as [H1 | H1]; try discriminate H1.
  rewrite in_flat_map.
  rewrite orl_map in H1.
  firstorder.

- destruct H1 as [H1 | [H1 | H1] ]; try discriminate.

  + firstorder.

  + rewrite in_app_iff, in_flat_map.
    rewrite orl_map in H1.
    firstorder.

- firstorder.
Qed.

Lemma ℐᵃ_wf : forall π p, wf π -> In p (ℐᵃ π) -> wf p.
Proof.
intros π p H1; revert p; induction π as [ lp t v IH | lp p' t v IH1 IH2 | i s p' t v IH ] using cbv_ind2; intros p H2; simpl in * |-.

- destruct t as [ x | c lt | f lt ]; try tauto.
  destruct v as [ c' lv ].
  destruct H1 as (H1 & H3 & H4 & H5).
  subst c' lt lv.
  rewrite in_flat_map in H2.
  destruct H2 as (p' & H2 & H3).
  apply IH with p'; trivial.
  apply andl_in with (P := wf p') in H5; trivial.
  apply in_map_iff.
  firstorder.

- destruct p' as [ lp' t' v' | lp' p' t' v' | i s p' t' v' ]; try tauto.
  destruct t' as [ x | c lt | f lt ]; try tauto.
  destruct t as [ x | c lt' | f' lt' ]; try tauto.
  destruct H1 as (H1 & H3 & H4 & H5 & H6 & H7).
  subst lt lt' f' v'.
  rewrite in_app_iff in H2.
  destruct H2 as [ H2 | H2 ]; auto.
  rewrite in_flat_map in H2.
  destruct H2 as (p'' & H2 & H5).
  apply (IH1 _ H2); trivial.
  apply (andl_in _ _ H4); rewrite in_map_iff; exists p''; tauto.

- destruct t as [ x | c lt | f lt ]; try tauto.
  destruct H1 as (lp & t & H0 & H1 & H3 & H4 & H5 & H6).
  destruct H2 as [ H2 | H2 ]; auto.
  subst lt v p.
  destruct p' as [ lp' t' v | lp' p t' v | j s' p t' v ]; firstorder.
Qed.

Lemma le_max_active_size π p :
  In p (ℐᵃ π) -> ╎proj_left p╎ + value_size (proj_right p) <= max_active_size π.
Proof.
intro H.
induction π as [ lp t v IH | lp p' t v IH_lp IH_p' | i s p' t v IH ] using cbv_ind2; simpl in *.

- rewrite in_flat_map in H.
  destruct H as (p' & H1 & H2).
  etransitivity.

  + apply IH.
    eexact H1.
    exact H2.

  + apply maxl_is_max.
    rewrite in_map_iff.
    exists p'; split; trivial.

- rewrite in_app_iff in H.
  destruct H as [H | H].

  + etransitivity.

    * apply IH_p'.
      exact H.

    * apply le_max_l.

  + rewrite in_flat_map in H.
    destruct H as (p'' & H1 & H2).
    etransitivity.

    * apply IH_lp.
      eexact H1.
      exact H2.

    * etransitivity; [idtac | apply le_max_r].
      apply maxl_is_max.
      apply in_map_iff.
      exists p''.
      tauto.

- destruct H as [H | H].

  + subst p.
    simpl in *.
    etransitivity; [idtac | apply le_max_l].
    trivial.

  + etransitivity; [idtac | apply le_max_r].
    apply IH.
    exact H.
Qed.

Hypothesis prog_is_wf : wf_prog max_arity prog.

Lemma 𝓡_spec :
  forall π, wf π -> forall p, In p (ℐᵃ π) ->
  let (i, s) := rule_subst_of_cbv_function p in
  ╎subst s (rhs_of_rule (nth i prog rule_default))╎ <= 𝓡 prog (╎proj_left p╎).
Proof.
intros π H_wf_π p H_p_activation.
case_eq (rule_subst_of_cbv_function p).
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
    generalize (activation_is_function H_p_activation); intros (i' & s' & p' & t' & v & H_p_is_function).
    subst p.
    simpl in H_p_fun.
    injection H_p_fun; clear H_p_fun; intros; subst i' s'.
    simpl in H_wf_p.
    destruct t'; try tauto.
    destruct H_wf_p as (lp & t' & H); tauto.

- apply plus_le_compat_l.
  transitivity (max_size_image_subst l s).

  + apply incl_le_max_size_image_subst.
    assert (rule_vars_defined rule_i) as H_wf_rule_i.
    * { eapply andl_in.

      - destruct prog_is_wf as [ Hwfrule _ ].
        exact Hwfrule.

      - rewrite in_map_iff.
        exists rule_i.
        split; trivial.
        apply nth_In.
        generalize (ℐᵃ_wf H_wf_π H_p_activation); intro H_wf_p.
        generalize (activation_is_function H_p_activation); intros (i' & s' & p' & t' & v & H_p_is_function).
        subst p.
        simpl in H_p_fun.
        injection H_p_fun; clear H_p_fun; intros; subst i' s'.
        simpl in H_wf_p.
        destruct t'; try tauto.
        destruct H_wf_p as (lp & t' & H); tauto. }

    * { destruct rule_i as [f lp t'].
        simpl in H_wf_rule_i.
        unfold l, r.
        simpl.
        replace (flat_map (@vars_of_term _ _ _) (map (@term_from_pattern _ _ _) lp)) with (flat_map (@vars_of_pattern _ _) lp).

          - exact H_wf_rule_i.

          - apply flat_map_comp; intros; apply vars_of_pattern_term. }

  + assert (subst s l = t) as H_t_matches_lhs.

    * generalize (ℐᵃ_wf H_wf_π H_p_activation); intro H_wf_p.
      generalize (activation_is_function H_p_activation); intros (i' & s' & p' & t' & v & H_p_is_function).
      unfold t; clear t.
      subst p.
      simpl.
      simpl in H_p_fun.
      injection H_p_fun; clear H_p_fun; intros; subst i' s'.
      simpl in H_wf_p.
      destruct t' as [ | | f lt]; try tauto.
      destruct H_wf_p as (lp & t' & H1 & H2 & H3 & H4 & H5 & H6).
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

(** Number of judgements *)
Fixpoint nb_judgements (π : cbv) : nat :=
  match π with
  | cbv_constr lp _ _ => 1 + suml (map nb_judgements lp)
  | cbv_split lp p _ _ => 1 + nb_judgements p + suml (map nb_judgements lp)
  | cbv_function _ _ p _ _ => 1 + nb_judgements p
  end.

(** Number of passive judgements *)
Fixpoint nb_judgements_sub_rec (π : cbv) : nat :=
  match π with
  | cbv_constr lp _ _ => 1 + suml (map nb_judgements_sub_rec lp)
  | cbv_split lp p _ _ => 1 + nb_judgements_sub_rec p + suml (map nb_judgements_sub_rec lp)
  | cbv_function _ _ _ _ _ => 0
  end.

Definition nb_judgements_sub (π : cbv) : nat :=
  match π with
  | cbv_constr _ _ _ => 0
  | cbv_split _ _ _ _ => 0
  | cbv_function _ _ p _ _ => nb_judgements_sub_rec p
  end.

Lemma nb_judgements_bound i s p' t v :
  let p := cbv_function i s p' t v in
  nb_judgements p <= suml (map nb_judgements_sub (ℐᵃ p)) + length (ℐᵃ p).
Proof.
induction p' as [ lp t' v' IH1 | lp p t' v' IH1 IH2 | i' s' p t' v' IH ] using cbv_ind2; simpl in *.

- apply le_n_S.
  rewrite length_flat_map.
  induction lp as [ | p lp IH2]; trivial.
  simpl.
  repeat match goal with |- context [ S (?m + ?n) ] => replace (S (m + n)) with (m + S n) by ring end.
  etransitivity.

  + apply plus_le_compat.

    * { apply le_S_n.
        etransitivity.

        - apply IH1; simpl; tauto.

        - match goal with |- ?m + S ?n <= _ => instantiate (1 := m + n) end.
          omega. }

    * apply IH2.
      intros p' Hp'; apply IH1; simpl; tauto.

  + rewrite map_app, suml_app.
    omega.

- apply le_n_S.
  rewrite map_app, suml_app, app_length, length_flat_map.
  induction lp as [ | p' lp IH3]; simpl; try omega.
  repeat match goal with |- context [ S (?m + (?n + ?p)) ] => replace (S (m + (n + p))) with (n + S (m + p)) by ring end.
  etransitivity.

  + apply plus_le_compat.

    * { apply le_S_n.
        etransitivity.

        - apply IH1; simpl; tauto.

        - match goal with |- ?m + S ?n <= _ => instantiate (1 := m + n) end.
          omega. }

    * apply IH3.
      intros p'' Hp''; apply IH1; simpl; tauto.

  + rewrite map_app, suml_app.
    omega.

- omega.
Qed.

Lemma nb_judgements_sub_rec_bound p :
  wf p -> nb_judgements_sub_rec p <= ╎proj_left p╎.
Proof.
intros H_wf_p.
induction p as [ lp t v IH | lp p t v IH _ | n s p t v _ ] using cbv_ind2; simpl in *.

- destruct t as [ | c lt | ]; try tauto.
  destruct v as [ c' lv ].
  simpl.
  apply le_n_S.
  destruct H_wf_p as (_ & H_lt & _ & H_wf); clear c'.
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

- destruct p as [ | | i s p t' v']; try tauto.
  destruct t' as [ | | f lt]; try tauto.
  destruct t as [ | | f' lt']; try tauto.
  simpl in *.
  apply le_n_S.
  destruct H_wf_p as (H1 & H2 & H3 & H4 & H5 & lp' & t & H6 & H7 & H8 & H9 & H10 & H11); subst; subst.
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
Qed.

Lemma nb_judgements_sub_bound i s p t v :
  wf (cbv_function i s p t v) ->
  nb_judgements_sub (cbv_function i s p t v) <= 𝓡 prog (╎t╎).
Proof.
intros H_wf_proof_tree.
assert (In (cbv_function i s p t v) (ℐᵃ (cbv_function i s p t v))) as H_p_activation.

- simpl; tauto.

- generalize (ℐᵃ_wf H_wf_proof_tree H_p_activation); intro H_wf_p.
  generalize (𝓡_spec H_wf_proof_tree H_p_activation).
  simpl; intro H.
  transitivity (╎subst s (rhs_of_rule (nth i prog rule_default))╎); [clear H | trivial].
  transitivity (╎proj_left p╎).

  + apply nb_judgements_sub_rec_bound; trivial.
    apply (wf_cbv_function H_wf_p).

  + simpl in H_wf_p.
    destruct t; try tauto.
    destruct H_wf_p as (lp & t & _ & H_rule & _ & H_proj & _).
    rewrite H_rule, H_proj; simpl.
    trivial.
Qed.

Lemma value_size_bounded_by_nb_judgements p :
  wf p -> value_size (proj_right p) <= nb_judgements p.
Proof.
intro H.
induction p as [ lp t v IH | lp p t v _ IH | n s p t v IH ] using cbv_ind2; simpl in *.

- destruct t as [ | c lt | ]; try tauto.
  destruct v as [ c' lv ].
  destruct H as (H1 & H2 & H3 & H4).
  subst c' lt lv.
  simpl.
  apply le_n_S.
  rewrite map_map.
  apply suml_map_le.
  intros p H1; apply IH; trivial.
  apply andl_in with (map wf lp); trivial.
  apply in_map_iff.
  exists p.
  tauto.

- destruct p as [ | | n s p t' v']; try tauto.
  destruct t' as [ | | f lv]; try tauto.
  destruct t as [ | | f' lt]; try tauto.
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6).
  subst lt lv f' v'.
  simpl in *.
  apply IH in H6; clear IH.
  etransitivity.

  + eexact H6.

  + omega.

- destruct t as [ | | f lv]; try tauto.
  destruct H as (lp & t & H1 & H2 & H3 & H4 & H5 & H6).
  subst lv v.
  apply le_S.
  tauto.
Qed.

Lemma term_size_bound_constr lp t v :
  wf (cbv_constr lp t v) ->
  andl (map (fun p => ╎t╎ >= ╎proj_left p╎) lp).
Proof.
simpl; intro H.
destruct t as [ | c lt | ]; try tauto.
destruct v as [ c' lv ].
destruct H as (H1 & H2 & H3 & H4).
subst c' lt lv.
eapply andl_map.

- eexact H4.

- intros p H1 H2.
  simpl.
  unfold ge.
  apply le_S.
  apply in_le_suml.
  apply in_map_iff.
  exists (proj_left p).
  split; trivial.
  apply in_map_iff.
  exists p.
  tauto.
Qed.

Lemma term_size_bound_split lp p t v :
  wf (cbv_split lp p t v) ->
  andl (map (fun p => ╎t╎ >= ╎proj_left p╎) lp).
Proof.
simpl; intro H.
destruct p as [ | | i s p t' v']; try tauto.
destruct t' as [ | | f lv]; try tauto.
destruct t as [ | | f' lt]; try tauto.
destruct H as (H1 & H2 & H3 & H4 & H5 & H6).
subst lt lv f' v'.
simpl in *.
destruct H6 as (lp' & t & H1 & H2 & H4 & H5 & H6 & H7).
subst v.
eapply andl_map.

- eexact H3.

- intros p' H6 H8.
  unfold ge.
  apply le_S.
  apply in_le_suml.
  apply in_map_iff.
  exists (proj_left p').
  split; trivial.
  apply in_map_iff.
  exists p'.
  tauto.
Qed.

Lemma size_bounded_nb_size_judgements p :
  size p <= nb_judgements p * max_judgement_size p.
Proof.
induction p as [ lp t v IH_lp | lp p t v IH_lp IH_p | i s p t v IH_p] using cbv_ind2; simpl.

- etransitivity.

  + apply plus_le_compat_l.
    apply suml_map_le in IH_lp.
    apply IH_lp.

  + set (a := ╎t╎ + value_size v).
    set (f := nb_judgements).
    set (g := max_judgement_size).
    apply plus_le_compat.

    * apply le_max_l.

    * { etransitivity.

        - apply suml_map_mult_le_suml_mult_maxl.

        - apply mult_le_compat_l.
          apply le_max_r.
      }

- etransitivity.

  + rewrite <- plus_assoc.
    apply plus_le_compat_l.
    apply plus_le_compat.

    * apply IH_p.

    * apply suml_map_le in IH_lp.
      apply IH_lp.

  + set (a := ╎t╎ + value_size v).
    set (f := nb_judgements).
    set (g := max_judgement_size).
    apply plus_le_compat.

    * apply le_max_l.

    * { etransitivity.

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
    apply IH_p.

  + set (a := nb_judgements p).
    set (b := max_judgement_size p).
    rewrite <- plus_assoc.
    set (c := ╎t╎ + value_size v).
    rewrite plus_comm.
    apply plus_le_compat.

    * apply le_max_l.

    * apply mult_le_compat_l.
      apply le_max_r.
Qed.

Lemma nb_judgements_sub_bound_gen : forall p p',
  let S := max_active_size p in
  wf p ->
  In p' (ℐᵃ p) -> nb_judgements_sub p' <= 𝓡 prog S.
Proof.
intros p p' S H_wf_p Hp'.
assert (wf p') as H1. {
  apply ℐᵃ_wf with p.
  exact H_wf_p.
  assumption.
}
generalize Hp'; intro H2p'.
apply activation_is_function in Hp'.
apply le_max_active_size in H2p'.
destruct Hp' as (i' & s' & p'' & t' & v' & Hp').
subst p'.
etransitivity.

- apply nb_judgements_sub_bound.
  assumption.

- simpl in H1.
  destruct t' as [ | | f lv]; try omega.
  destruct H1 as (lp & t' & H1 & H2 & H3 & H4 & H5 & H6).
  subst lv v'.
  simpl in H2p'.
  apply 𝓡_monotone.
  etransitivity; [idtac | apply H2p'].
  simpl; omega.
Qed.

Lemma nb_judgements_bound_gen : forall i s p' t v,
  let p := cbv_function i s p' t v in
  let A := length (ℐᵃ p) in
  let S := max_active_size p in
  wf p ->
  nb_judgements p <= A * 𝓡 prog S + A.
Proof.
intros i s p' t v p A S H_wf_p.
etransitivity.
apply nb_judgements_bound.
unfold A, p.
apply plus_le_compat_r.
set (list_activ := ℐᵃ (cbv_function i s p' t v)).
etransitivity.

- apply suml_le_len_times_bound.
  instantiate (1 := 𝓡 prog S).
  intros x H_x.
  apply in_map_iff in H_x.
  destruct H_x as [ p'' [ H_x1 H_x2 ]].
  subst x.
  apply nb_judgements_sub_bound_gen; trivial.

- apply mult_le_compat_r.
  rewrite map_length.
  trivial.
Qed.

(** Bound on the size of the term *)
Lemma term_size_proj_left_bound : forall i s p' t v,
  let p := cbv_function i s p' t v in
  let S := max_active_size p in
  wf p ->
  forall p',
  InCBV p' p -> ╎proj_left p'╎ <= 𝓡 prog S + S.
Proof.
(** we use cbv_reverse_induction to prove ≤ activation S + S
   - base case: as a cbv_function it is bounded by S
   - inductive case:
     - the sub-tree of a cbv_function is bounded by act S,
     - the sub-trees of a cbv_constr are bounded by the cbv_constr itself,
     - the subtrees in the lp of a cbv_split are bounded by the cbv_split itself,
     - the subtree p of a cbv_split is a cbv_function, thus bounded by S *)

intros i s p0 t v p S H_wf_p.
apply cbv_reverse_induction.

- (* Base case *)
  transitivity S.

  + unfold p, S.
    simpl.
    transitivity (╎t╎ + value_size v).

    * apply le_plus_l.

    * apply le_max_l.

      + apply le_plus_r.

- (* cbv_constr *)
  intros lp t' v' H_p'_in_p IH p'' H_p''_in_lp.
  transitivity (╎proj_left (cbv_constr lp t' v')╎).

  + generalize (wf_InCBV_wf H_wf_p H_p'_in_p).
    simpl.
    destruct t'; try (intro H_false; destruct H_false).
    destruct v'.
    intros [ H_c0 [ H_l_lp [ _ H_wf_lp ] ] ].
    rewrite <- H_c0 in *; clear H_c0.

    simpl.
    rewrite H_l_lp.
    apply le_S.
    apply in_le_suml.
    apply in_map.
    apply in_map.
    apply H_p''_in_lp.

    + apply IH.

- (* cbv_split *)
  intros lp p' t' v' H_in_p IH p'' H_p''_in.
  destruct H_p''_in as [ H_p''_in | H_p''_in ].

  + (* if p'' = p', then p' is a cbv_function *)
  { rewrite H_p''_in.
    transitivity S.
    transitivity (╎proj_left p'╎ + value_size (proj_right p')).

    - apply le_plus_l.

    - apply le_max_active_size.
      generalize (wf_InCBV_wf H_wf_p H_in_p).
      intro H_wf_split.
      simpl in H_wf_split.
      destruct p'; try tauto.
      apply cbv_function_in_ℐᵃ_InCBV with n v0 p' t0 v1; try auto.
      apply InCBV_trans with (cbv_split lp (cbv_function n v0 p' t0 v1) t' v').

      * simpl.
        tauto.

      * apply H_in_p.

    - apply le_plus_r.
  }

  + (* if p'' ∈ lp, then similarly as the cbv_constr case *)
    transitivity (╎proj_left (cbv_split lp p' t' v')╎).

    * generalize (wf_InCBV_wf H_wf_p H_in_p).
      simpl.
      destruct p'; try tauto.
      destruct t0; try tauto.
      destruct t' as [ | | f' lt ]; try tauto.
      intros [ H_lt_lp [ _ [ _ [ H_f [ H_v _ ] ] ] ] ].
      rewrite <- H_f in *; clear H_f.
      rewrite H_v in *; clear H_v.
      rewrite H_lt_lp in *; clear H_lt_lp.
      simpl.
      apply le_S.
      apply in_le_suml.
      apply in_map.
      apply in_map.
      assumption.

    * assumption.

- (* cbv_function *)
  intros i' s' p' t' v' H_in_p IH.
  transitivity (𝓡 prog (╎t'╎)).

  + change t' with (proj_left (cbv_function i' s' p' t' v')).
    replace (proj_left p') with (subst s' (rhs_of_rule (nth i' prog rule_default))).

    * generalize (@𝓡_spec p H_wf_p (cbv_function i' s' p' t' v')).
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
          apply (@cbv_function_in_ℐᵃ_InCBV p0 (cbv_function i' s' p' t' v') i' s' p' t' v'); trivial.
      }

    * generalize (wf_InCBV_wf H_wf_p H_in_p).
      simpl.
      destruct t'; try tauto.
      intros [ lp [ t' [ _ [ H_nth_rule [ _ [ H_proj_subst _ ] ] ] ] ] ].
      rewrite H_proj_subst.
      f_equal.
      rewrite H_nth_rule.
      simpl.
      trivial.

  + apply le_plus_trans.
    apply 𝓡_monotone.
    transitivity (╎proj_left (cbv_function i' s' p' t' v')╎ + value_size (proj_right (cbv_function i' s' p' t' v'))).

    * apply le_plus_trans.
      simpl.
      trivial.

    * apply le_max_active_size.
      apply cbv_function_in_ℐᵃ_InCBV with i' s' p' t' v'; trivial.
Qed.

(** Bound on the size of judgements *)
Lemma size_judgement : forall i s p' t v,
  let p := cbv_function i s p' t v in
  let A := length (ℐᵃ p) in
  let S := max_active_size p in
  wf p ->
  max_judgement_size p <= 𝓡 prog S + S + A * 𝓡 prog S + A.
Proof.
  (* We bound the size of terms in judgements *)
  (* terms in ℐᵃ are bounded by S by definition.
     For passive judgements, we do a case analysis on the next judgement:
     - if it is an activation, we apply activaction_bound_spec.
     - otherwise, the size is bounded by the proj_left of the next judgement, so
        we use term_size_bound *)

  (* Then we bound the size of values in judgements with value_size_bounded_by_nb_judgements *)

  intros i s p0 t v p A S H_wf_p.
  etransitivity.
  apply judgement_size_le_projs_size.
  rewrite <- plus_assoc.
  apply plus_le_compat.

  + apply term_size_proj_left_bound; trivial.
    apply InCBV_proj_left_max_size.

  + transitivity (nb_judgements p).

    * { (*wa apply value_size_bounded_by_nb_judgements. *)
        generalize H_wf_p.
        clear H_wf_p.
        intro H_wf_p.
        induction p as [ lp t' v' IH | lp p' t' v' IH_lp IH_p' | i' s' p' t' v' IH ] using cbv_ind2.

        - simpl max_proj_right_size.
          destruct (max_dec (value_size v') (maxl (map max_proj_right_size lp))) as [ H_max | H_max ]; rewrite H_max.

          + change v' with (proj_right (cbv_constr lp t' v')) at 1.
            apply value_size_bounded_by_nb_judgements.
            assumption.

          + simpl.
            apply le_S.
            transitivity (maxl (map nb_judgements lp)).

            * apply maxl_le_maxl.
              intros p' H_in_lp.
              apply IH.
              assumption.
              apply (wf_InCBV_wf H_wf_p).
              simpl.
              right.
              apply orl_map.
              exists p'.

              split.
              trivial.
              apply InCBV_refl.

            * apply maxl_le_suml.

        - simpl max_proj_right_size.
          destruct (max_dec (value_size v') (max (max_proj_right_size p') (maxl (map max_proj_right_size lp)))) as [H_max | H_max ]; rewrite H_max; clear H_max.

          + change v' with (proj_right (cbv_split lp p' t' v')).
            apply value_size_bounded_by_nb_judgements.
            assumption.

          + simpl.
            apply le_S.
            destruct (max_dec (max_proj_right_size p') (maxl (map max_proj_right_size lp))) as [ H_max | H_max ]; rewrite H_max; clear H_max.

            * apply le_plus_trans.
              apply IH_p'.
              apply (wf_InCBV_wf H_wf_p).
              simpl; right; left; apply InCBV_refl.

            * rewrite plus_comm.
              apply le_plus_trans.

              { transitivity (maxl (map nb_judgements lp)).

                + apply maxl_le_maxl.
                  intros p'' H_in_lp.
                  apply IH_lp.
                  assumption.
                  apply (wf_InCBV_wf H_wf_p).
                  simpl.
                  right; right.
                  apply orl_map.
                  exists p''.

                  split.
                  trivial.
                  apply InCBV_refl.

                + apply maxl_le_suml.
              }

        - simpl max_proj_right_size.
          destruct (max_dec (value_size v') (max_proj_right_size p')) as [H_max | H_max ]; rewrite H_max; clear H_max.

          + change v' with (proj_right (cbv_function i' s' p' t' v')).
            apply value_size_bounded_by_nb_judgements.
            assumption.

          + simpl.
            apply le_S.
            apply IH.
            apply (wf_InCBV_wf H_wf_p).
            simpl; right; apply InCBV_refl.
      }

    * apply nb_judgements_bound_gen; trivial.
Qed.

Theorem size_bound : forall i s p' t v,
  let p := cbv_function i s p' t v in
  let A := length (ℐᵃ p) in
  let S := max_active_size p in
 wf p ->
  size p <=
  (A * 𝓡 prog S + A) * (𝓡 prog S + S + A * 𝓡 prog S + A).
Proof.
intros i s p0 t v p A S H_wf_p.
etransitivity.
- apply size_bounded_nb_size_judgements.
- apply mult_le_compat.

  + apply nb_judgements_bound_gen; trivial.

  + apply size_judgement; trivial.
Qed.

End CBV.
