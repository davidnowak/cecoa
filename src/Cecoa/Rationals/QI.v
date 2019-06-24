(** * Quasi-Interpretations *)
Require Import QArith Le Max List Bool Cecoa.Rationals.Lib Cecoa.Rationals.Syntax Cecoa.Rationals.CBV_cache NPeano Omega Cecoa.Rationals.OptionMonad.

Section QI.

Open Scope Q.

Variables variable function constructor : Type.

Notation value := (Syntax.value constructor).
Notation term := (Syntax.term variable function constructor).
Notation pattern := (Syntax.pattern variable constructor).
Notation rule := (Syntax.rule variable function constructor).
Notation term_from_value := (Syntax.term_from_value variable function (constructor:=constructor)).
Notation term_from_pattern := (Syntax.term_from_pattern (variable:=variable) function (constructor:=constructor)).
Notation "'╎' t '╎'" := (@term_size variable function constructor t) (at level 10).
Variable prog : list rule.
Variable max_arity:nat.
Variable rule_default : rule.

Variable variable_eq_dec : forall (x1 x2 : variable), {x1=x2}+{x1<>x2}.
Variable function_eq_dec : forall (x1 x2 : function), {x1=x2}+{x1<>x2}.
Variable constructor_eq_dec : forall (x1 x2 : constructor), {x1=x2}+{x1<>x2}.

Notation cache := (CBV_cache.cache variable function constructor).
Notation cache_path := (CBV_cache.cache_path variable_eq_dec function_eq_dec constructor_eq_dec).



Notation cache_path_transitivity :=
           (@CBV_cache.cache_path_transitivity _ _ _ variable_eq_dec function_eq_dec constructor_eq_dec).
Notation cache_path_transitivity_left :=
           (@CBV_cache.cache_path_transitivity_left _ _ _ variable_eq_dec function_eq_dec constructor_eq_dec).
Notation cbv := (CBV_cache.cbv variable function constructor).
Notation wf := (CBV_cache.wf variable_eq_dec  function_eq_dec constructor_eq_dec rule_default
                prog max_arity).

(** ** Assignments *)

Definition assignment_constructor := constructor -> list Qpos -> Qpos.
Definition assignment_function := function -> list Qpos -> Qpos.

(*****************************************************************************************)
(*                  QI of constructors / value                                           *)
(*****************************************************************************************)

(* additivity*)
Variable mcs: Qpos.

Definition constructor_non_zero cs :=
   forall c:constructor, cs  c >= 1.

Definition additive (qic:assignment_constructor) cs :=
   forall c:constructor, forall l, qic c l=Qpos_plus (qsuml l) (cs c).

Definition mcs_is_max_constructor_size cs :=
    forall c:constructor, cs c <= mcs.

Lemma monotonicity_qic qic cs: additive qic cs -> forall c:constructor,
  forall (lx ly : list Qpos), Forall2 Qposle lx ly -> qic c lx <= qic c ly.
Proof.
intro additivity;intros.
unfold additive in additivity.
rewrite additivity;rewrite additivity.
apply Qplus_le_compat; auto with *.
induction H;auto with *; simpl.
destruct qsuml; simpl.
destruct qsuml; simpl.
apply Qplus_le_compat;trivial.
Qed.

(* assignment of a value*)
Fixpoint value_assignment (qic:assignment_constructor) (v:value) {struct v}:=
   match v with
  | c_capply c lv => qic c (map (value_assignment qic) lv)
   end.

(* Lower bound *)
Lemma value_size_le_QI qic cs:
  additive qic cs -> constructor_non_zero cs ->
  forall v:value, Qpos_of_nat (value_size v) <= value_assignment qic v.
Proof.
intros additivity non_zero.
unfold additive in additivity. unfold constructor_non_zero in non_zero.
induction v using value_ind2.
simpl.
apply Qle_trans with (y:= qsuml (map (value_assignment qic) l)+1).
- rewrite Zpos_P_of_succ_nat.
  unfold Z.succ.
  rewrite inject_Z_plus.
  simpl inject_Z.
  apply Qplus_le_compat; auto with *.
  induction l; simpl; auto with *.
  rewrite Nat2Z.inj_add, inject_Z_plus.
  destruct qsuml; simpl.
  apply Qplus_le_compat; auto with *.
  apply H; auto with *.
- simpl.
  rewrite additivity.
  apply Qplus_le_compat; auto with *.
Qed.

(* Upper bound *)
Lemma QI_le_value_size qic cs:
  additive qic cs -> mcs_is_max_constructor_size cs ->
  forall v:value,
  value_assignment qic v <= mcs * (Qpos_of_nat (value_size v)).
Proof.
intros additivity max_cs.
unfold additive in additivity. unfold mcs_is_max_constructor_size in max_cs.
induction v using value_ind2.
simpl.
rewrite additivity.
apply Qle_trans with (y:= qsuml (map (value_assignment qic) l)+mcs).
- apply Qplus_le_compat; auto with *.
- rewrite Zpos_P_of_succ_nat.
  unfold Z.succ.
  rewrite inject_Z_plus.
  ring_simplify.
  apply Qplus_le_compat; auto with *.
  induction l; simpl; ring_simplify; auto with *.
  rewrite Nat2Z.inj_add, inject_Z_plus.
  ring_simplify.
  destruct qsuml; simpl.
  apply Qplus_le_compat; auto with *.
  apply H; auto with *.
Qed.

(*****************************************************************************************)
(*                  QI of function symbols / terms                                       *)
(*****************************************************************************************)

(** Subterm *)
Definition subterm (qif:assignment_function) :=
  forall f (l :list Qpos) x, In x l -> x <= qif f l.

(** Monotonicity *)
Definition monotonicity_qif (qif:assignment_function) :=
  forall f (lx ly : list Qpos), Forall2 Qposle lx ly -> qif f lx <= qif f ly.

(** Assignment of a term (Definition 41) *)
Fixpoint term_assignment (qic:assignment_constructor) (qif:assignment_function)
(t:term) {struct t} : Qpos:=
   match t return Qpos with
  | var v=> exist _ 0 Lib.qmaxl_obligation_1 (* QI are always applied on closed terms anyway *)
  | capply c lt => qic c (map (term_assignment qic qif) lt)
  | fapply f lt=> qif f (map (term_assignment qic qif)  lt)
 end.

(*Definition 12*)
Definition compatible_QI qic qif := forall f lp t, forall s:variable -> value,
  let ru := rule_intro f lp t in (* f(p1, ..., pn) -> t *)
  (In ru prog) ->
  term_assignment qic qif (subst s t) <= term_assignment qic qif (subst s (lhs_of_rule ru)).

Definition valid_QI qic qif cs :=
  (additive qic cs) /\ (mcs_is_max_constructor_size cs) /\ (constructor_non_zero cs) /\
  (subterm qif) /\ (monotonicity_qif qif) /\ (compatible_QI qic qif).

Definition cache_bounded qic qif (c:cache): Prop  :=
  Forall (fun t => value_assignment qic (snd t) <= term_assignment qic qif (fst t)) c.

Lemma value_as_term_assignment qic qif: forall v:value,
  (term_assignment qic qif (term_from_value v)) = (value_assignment qic v).
Proof.
induction v using value_ind2.
simpl.
rewrite map_map.
apply f_equal2;trivial.
apply map_in_ext;trivial.
Qed.


(*****************************************************************************************)
(*                        starting real proofs                                           *)
(*****************************************************************************************)

(* The following lemmas are used twice in the following *)
Lemma qi_fapply_right_le_qi_fapply_left qic qif : forall π lp f c1,
  monotonicity_qif qif ->
  let l := map (proj_left (constructor:=constructor)) lp in
  let l' := map term_from_value (map (proj_right (constructor:=constructor)) lp) in
  let c := cache_left π in let v := proj_right π in
  (forall p, In p lp -> cache_bounded qic qif (cache_left p) ->
             value_assignment qic (proj_right p) <= term_assignment qic qif (proj_left p) /\
             cache_bounded qic qif (cache_right p)) ->
  cache_bounded qic qif c1 -> cache_path c1 c lp = true -> andl (map wf lp) ->
  (term_assignment qic qif (fapply f l')) <= (term_assignment qic qif (fapply f l)).
Proof.
intros π lp f c1 monotonicity l l' c v.
intros lp_bound c1_bound c_path wf_lp.
simpl.
unfold monotonicity_qif in monotonicity.
apply monotonicity.
unfold l;unfold l';clear l l'.
rewrite map_map;rewrite map_map;rewrite map_map.
apply Forall2_map.
intros.
rewrite value_as_term_assignment.
apply lp_bound;auto.
apply cache_path_transitivity_left with (c:=c1) (c':=c) (l:=lp);auto.
apply lp_bound.
Qed.

Lemma qi_right_le_qi_fapply_left qic qif: forall π lp f c1,
  monotonicity_qif qif -> wf π ->
  let l := map (proj_left (constructor:=constructor)) lp in
  let l' := map term_from_value (map (proj_right (constructor:=constructor)) lp) in
  let c := cache_left π in let c' := cache_right π in
  let v := proj_right π in
  proj_left π = fapply f l' ->
  (forall p, In p lp -> cache_bounded qic qif (cache_left p) -> wf p ->
             value_assignment qic (proj_right p) <= term_assignment qic qif (proj_left p) /\
             cache_bounded qic qif (cache_right p)) ->
  (cache_bounded qic qif c -> value_assignment qic v <= term_assignment qic qif (fapply f l')) ->
  cache_bounded qic qif c1 -> cache_bounded qic qif c' -> cache_path c1 c lp = true ->
    andl (map wf lp) ->
  value_assignment qic v <= term_assignment qic qif (fapply f l).
Proof.
intros π lp f c1 monotonicity well_formed l l' c c' v.
intros pl lp_bound val_bound c1_bound c'_bound c_path wf_lp.
apply Qle_trans with (y:=term_assignment qic qif (fapply f l'));auto.
- apply val_bound;auto.
  apply cache_path_transitivity with (c:=c1) (c':=c) (l:=lp);auto.
  intros;apply lp_bound;auto.
  apply andl_in_map with (l:=lp);auto.
- apply qi_fapply_right_le_qi_fapply_left with (π:=π) (c1:=c1);try tauto.
  intros.
  apply lp_bound;try tauto.
  apply andl_in_map with (l:=lp);auto.
Qed.

(** Lemma 63 *)
Lemma left_bound_to_right_bound qic qif cs:forall pi:cbv,
    valid_QI qic qif cs -> (wf pi) ->
    cache_bounded qic qif (cache_left pi) ->
    (value_assignment qic (proj_right pi) <= term_assignment qic qif (proj_left pi)
     /\ cache_bounded qic qif (cache_right pi)).
Proof.
intros pi valid.
unfold valid_QI in valid.
destruct valid as (additivity & mcs_is_max & non_zero & sub & mono & compat).
induction pi using cbv_ind2;
          unfold cache_left;unfold proj_right;unfold proj_left;unfold cache_right;
          intros well_formed cache.
- (* cbv_constr *)
  assert (cache_bounded qic qif c2).
  + (* prove bound on cache *)
    simpl in well_formed;destruct t;destruct v;try tauto.
    destruct well_formed as (cpath & Hc & Hl & Hl0 & wf_list & arity).
    apply cache_path_transitivity with (c:=c1) (c':=c2) (l:=lp);auto.
    intros;apply H;auto.
    apply andl_in_map with (l:=lp);auto.
  + (* bound on QI *)
    split;auto.
    simpl in well_formed;destruct t;destruct v;try tauto.
    destruct well_formed as (cpath & Hc & Hl & Hl0 & wf_list & arity).
    subst c.
    simpl;apply (monotonicity_qic qic cs);trivial.
    subst l l0.
    rewrite map_map;rewrite map_map.
    apply Forall2_map.
    intros.
    apply H;auto.
    * apply andl_in_map with (l:=lp);auto.
    * apply cache_path_transitivity_left with (c:=c1) (c':=c2) (l:=lp);auto.
      intros.
      apply H;auto.
      apply andl_in_map with (l:=lp);auto.
- (* cbv_split *)
  destruct t;simpl in well_formed;destruct pi;destruct t;try tauto.
  + (* cbv_update *)
    assert (cache_bounded qic qif c2).
    { destruct well_formed as (Hc2 & cpath &  Hl & Hl0 & wf_list & Hf & Hv & well_formed & arity).
      unfold cache_left in IHpi;unfold cache_right in IHpi.
      subst c2.
      apply IHpi;auto.
      apply cache_path_transitivity with (c:=c1) (c':=c) (l:=lp);auto.
      intros;apply H;auto.
      apply andl_in_map with (l:=lp);auto.
    }
    (* bound on QIs *)
    split;auto.
    destruct well_formed as (Hc2 & cpath &  Hl & Hl0 & wf_list & Hf & Hv & well_formed & arity).
    unfold cache_left, cache_right, proj_left, proj_right in IHpi.
    subst c2 l f0 v1.
    set (π:=cbv_update n v0 pi c (fapply f l0) c0 v).
    subst l0.
    apply qi_right_le_qi_fapply_left with (π:=π) (c1:=c1);try tauto.
    intros;apply H;trivial.
  + (* cbv_read *)
    assert (cache_bounded qic qif c2).
    {  destruct well_formed as (Hc2 & cpath &  Hl & Hl0 & wf_list & Hf & Hv & well_formed & arity).
      subst c2.
      apply cache_path_transitivity with (c:=c1) (c':=c) (l:=lp);auto.
      intros;apply H;auto.
      apply andl_in_map with (l:=lp);auto.
    }
    (* bound on QIs *)
    split;auto.
    destruct well_formed as (Hc2 & cpath &  Hl & Hl0 & wf_list & Hf & Hv & well_formed & arity).
    unfold cache_left in IHpi;unfold cache_right in IHpi.
    subst c2 l f0 v0.
    set (π:=cbv_read c (fapply f l0) v).
    subst l0.
    apply qi_right_le_qi_fapply_left with (π:=π) (c1:=c1);try tauto.
    intros;apply H;trivial.
- (* cbv_update *)
  assert (value_assignment qic v <= term_assignment qic qif t).
  { revert well_formed.
    elim t;simpl;try tauto.
    intros.
    destruct well_formed as (_ & lp & r & length & rule & Hl & pl & pr & cl & _ & _ & wf_pi & _).
    rewrite cl in *;clear cl.
    rewrite pl in *;clear pl.
    rewrite pr in *;clear pr.
    generalize (IHpi wf_pi cache).
    generalize (compat f lp r s).
    intros.
    replace (qif f (map (term_assignment qic qif) l)) with
	    (term_assignment qic qif (subst s (lhs_of_rule (rule_intro f lp r)))).
    * apply Qle_trans with (y:=term_assignment qic qif (subst s r));try tauto.
      apply H.
      rewrite <- rule;apply nth_In;auto.
    * simpl.
      rewrite Hl.
      rewrite (map_map (term_from_pattern) (subst s) lp).
      rewrite (map_map (psubst s) (term_from_value) lp).
      f_equal;f_equal.
      clear.
      induction lp as [ | p lp IH];simpl;trivial.
      rewrite IH.
      f_equal;apply subst_psubst.
  }
  (* prove bound on cache *)
  split;auto.
  simpl in well_formed.
  destruct t;try tauto.
  destruct well_formed as (_ & _ & _ & _  & _ & _ & _ & _ & cl & _ & new_cache & wf_pi & _).
  subst c2.
  unfold cache_bounded.
  apply Forall_cons.
  * unfold fst, snd;auto.
  * apply IHpi;auto.
    rewrite cl;auto.
- (* cbv_read *)
  split;auto.
  simpl in well_formed;destruct t;try tauto.
  destruct well_formed as (c_hit & lv'& Hl).
  unfold cache_bounded in cache.
  apply (Forall_In_l ((fapply f l),v) cache).
  apply (assoc_in (term_beq variable_eq_dec function_eq_dec constructor_eq_dec)
         (fapply f l) c);auto.
  apply (term_beq_eq variable_eq_dec function_eq_dec constructor_eq_dec).
Qed.

(***********************************************************************************)
(*                                                                                 *)
(*             Global bounds                                                       *)
(*                                                                                 *)
(***********************************************************************************)

(* Lemma 64 *)
Lemma QI_never_increase_global qic qif cs: forall pi π:cbv,
  valid_QI qic qif cs -> wf π ->
  cache_bounded qic qif (cache_left π) -> InCBV pi π ->
  term_assignment qic qif (proj_left pi) <= term_assignment qic qif (proj_left π).
Proof.
intros pi π valid well_formed cache subtree.
unfold valid_QI in valid.
destruct valid as (additivity & max_cs & non_zero & sub & mono & compat).
induction π using cbv_ind2.
- (* cbv_constr *)
  simpl in subtree;destruct subtree as [equal | strict].
  + (* equality *)
    subst pi; auto with *.
  + (* list sub-trees *)
    simpl in well_formed.
    destruct t;destruct v;try tauto.
    destruct well_formed as (cpath & Hc & Hl & Hl0 & wf_list & arity).
    rewrite orl_map in strict.
    destruct strict as (x & inlist & intree).
    apply Qle_trans with (y:=term_assignment qic qif (proj_left x)).
    * { apply H;trivial.
        - apply andl_in_map with (l:=lp);trivial.
        - apply cache_path_transitivity_left with (c:=c1) (c':=c2) (l:=lp);trivial.
          intros;apply (left_bound_to_right_bound qic qif cs);trivial.
          + unfold valid_QI;tauto.
          + apply andl_in_map with (l:=lp);trivial.
      }
    * simpl;subst l.
      rewrite additivity;rewrite map_map.
      apply Qle_trans with (y := term_assignment qic qif (proj_left x) + 0).
       {ring_simplify; auto with *. }
      apply Qplus_le_compat.
      -- apply in_le_qsuml, in_map_iff; eauto.
      -- destruct cs; trivial.
- (* cbv_split *)
  simpl in subtree;destruct subtree as [equal | [single | strict]].
  + (* equality *)
    subst pi; auto with *.
  + (* sub-tree *)
    simpl in well_formed.
    destruct π;destruct t0;destruct t;try tauto;intuition;
             subst f0 c2;try subst v1;try subst v0.
    * { simpl;simpl in cache;simpl in H8.
        simpl in single;destruct single as [equal | strict].
        (* identical cases *)
        - apply Qle_trans with (y:=qif f (map (term_assignment qic qif) l)).
          + apply H8;auto.
            apply cache_path_transitivity with (c:=c1) (c':=c) (l:=lp);trivial.
            intros;apply (left_bound_to_right_bound qic qif cs);trivial.
            * unfold valid_QI;tauto.
            * apply andl_in_map with (l:=lp);trivial.
          + apply mono.
            subst l l0.
            rewrite map_map;rewrite map_map;rewrite map_map.
            apply Forall2_map.
            intros.
            apply Qle_trans with (y:=value_assignment qic (proj_right x)). (* type coercion *)
            * rewrite value_as_term_assignment.
              auto with *.
            * apply (left_bound_to_right_bound qic qif cs);trivial.
              unfold valid_QI;tauto.
              apply andl_in_map with (l:=lp);trivial.
              apply cache_path_transitivity_left with (c:=c1) (c':=c) (l:=lp);trivial.
              intros;apply (left_bound_to_right_bound qic qif cs);trivial.
              unfold valid_QI;tauto.
              apply andl_in_map with (l:=lp);trivial.
        - apply Qle_trans with (y:=qif f (map (term_assignment qic qif) l)).
          + apply H8;auto.
            apply cache_path_transitivity with (c:=c1) (c':=c) (l:=lp);trivial.
            intros;apply (left_bound_to_right_bound qic qif cs);trivial.
            * unfold valid_QI;tauto.
            * apply andl_in_map with (l:=lp);trivial.
          + apply mono.
            subst l l0.
            rewrite map_map;rewrite map_map;rewrite map_map.
            apply Forall2_map.
            intros.
            apply Qle_trans with (y:=value_assignment qic (proj_right x)).
            * rewrite value_as_term_assignment.
              auto with *.
            * apply (left_bound_to_right_bound qic qif cs);trivial.
              unfold valid_QI;tauto.
              apply andl_in_map with (l:=lp);trivial.
              apply cache_path_transitivity_left with (c:=c1) (c':=c) (l:=lp);trivial.
              intros;apply (left_bound_to_right_bound qic qif cs);trivial.
              unfold valid_QI;tauto.
              apply andl_in_map with (l:=lp);trivial.
      }
    * (* cbv_read above *)
      simpl in cache;simpl in single;simpl in H8.
      destruct single as [equal | false];try tauto.
      subst pi;simpl in *.
      apply mono.
      subst l l0.
      rewrite map_map;rewrite map_map;rewrite map_map.
      apply Forall2_map.
      intros.
      { apply Qle_trans with (y:=value_assignment qic (proj_right x)).  (* type coercion *)
        - rewrite value_as_term_assignment.
          auto with *.
        - apply (left_bound_to_right_bound qic qif cs);trivial.
          + unfold valid_QI;tauto.
          + apply andl_in_map with (l:=lp);trivial.
          + apply cache_path_transitivity_left with (c:=c1) (c':=c) (l:=lp);trivial.
            intros;apply (left_bound_to_right_bound qic qif cs);trivial.
            * unfold valid_QI;tauto.
            * apply andl_in_map with (l:=lp);trivial.
      }
  + (* lists all sub-trees *)
    simpl in well_formed.
    destruct π;destruct t0;destruct t;try tauto;intuition;
             simpl;simpl in H9;simpl in cache;subst c2 f0;try subst v1;try subst v0.
    (* identical cases *)
    * (* cbv_update above *)
      { rewrite orl_map in strict.
        destruct strict as (x & inlist & intree).
        apply Qle_trans with (y:=term_assignment qic qif (proj_left x)).
        - apply H;trivial.
          + apply andl_in_map with (l:=lp);trivial.
          + apply cache_path_transitivity_left with (c:=c1) (c':=c) (l:=lp);trivial.
            intros;apply (left_bound_to_right_bound qic qif cs);trivial.
            * unfold valid_QI;tauto.
            * apply andl_in_map with (l:=lp);trivial.
        - subst l0;rewrite map_map.
          apply sub.
          apply in_map with (f:=fun x0 => term_assignment qic qif (proj_left x0));trivial.
      }
    * (* cbv_read above *)
      { rewrite orl_map in strict.
        destruct strict as (x & inlist & intree).
        apply Qle_trans with (y:=term_assignment qic qif (proj_left x)).
        - apply H;trivial.
          + apply andl_in_map with (l:=lp);trivial.
          + apply cache_path_transitivity_left with (c:=c1) (c':=c) (l:=lp);trivial.
            intros;apply (left_bound_to_right_bound qic qif cs);trivial.
            * unfold valid_QI;tauto.
            * apply andl_in_map with (l:=lp);trivial.
        - subst l0;rewrite map_map.
          apply sub.
          apply in_map with (f:=fun x0 => term_assignment qic qif (proj_left x0));trivial.
      }
- (* cbv_update *)
  simpl;simpl in cache.
  simpl in subtree;destruct subtree as [equal | strict].
  + (* equality *)
    subst pi; auto with *.
  + (* sub-tree *)
    simpl in well_formed.
    destruct t;try tauto.
    destruct well_formed as (_ & lp & t & n_le_lp & rule & Hl & pl & pr & cl & _ & _ & wf_ind & _).
    apply Qle_trans with (y:=term_assignment qic qif (proj_left π)).
    * subst c1;apply IHπ;trivial.
    * rewrite pl.
      simpl;unfold compatible_QI in compat.
      { replace l with (map (subst s) (map term_from_pattern lp)).
        - apply compat.
          rewrite <- rule;apply nth_In;trivial.
        - subst l.
          rewrite map_map;rewrite map_map.
          apply map_ext.
          intros;apply subst_psubst.
      }
- (* cbv_read *)
  simpl in subtree;destruct subtree as [equal | impossible];try tauto.
  subst pi; auto with *.
Qed.

Lemma cache_left_bounded_global qic qif cs: forall pi π:cbv,
  valid_QI qic qif cs -> wf π ->
  cache_bounded qic qif (cache_left π) -> InCBV pi π ->
  cache_bounded qic qif (cache_left pi).
Proof.
intros pi π valid well_formed cache subtree.
induction π using cbv_ind2.
- (* cbv_constr *)
  simpl in subtree;destruct subtree as [ equal | strict].
  + (* equality *)
    subst pi;trivial.
  + (* list sub-trees *)
    simpl in well_formed.
    destruct t;destruct v;try tauto.
    destruct well_formed as (cpath & Hc & Hl & Hl0 & wf_list & arity).
    rewrite orl_map in strict.
    destruct strict as (x & inlist & intree).
    apply H with (p:=x);auto.
    * apply andl_in_map with (l:=lp);trivial.
    * apply cache_path_transitivity_left with (c:=c1) (c':=c2) (l:=lp);auto.
      intros;apply (left_bound_to_right_bound qic qif cs);trivial.
      apply andl_in_map with (l:=lp);trivial.
- (* cbv_split *)
  simpl in subtree;destruct subtree as [equal | [single | strict]].
  + (* equality *)
    subst pi;trivial.
  + (* sub-tree *)
    simpl in well_formed.
    destruct π;destruct t0;destruct t;try tauto;intuition;simpl in cache.
    * (* cbv_update above *)
      apply H8;auto.
      simpl.
      apply cache_path_transitivity with (c:=c1) (l:=lp);auto.
      intros;apply (left_bound_to_right_bound qic qif cs);trivial.
      apply andl_in_map with (l:=lp);trivial.
    * (* cbv_read above *)
      simpl in single;destruct single as [equal | impossible];try tauto.
      subst pi;simpl.
      apply cache_path_transitivity with (c:=c1) (c':=c) (l:=lp);auto.
      intros;apply (left_bound_to_right_bound qic qif cs);trivial.
      apply andl_in_map with (l:=lp);trivial.
  + (* list sub-trees *)
    simpl in well_formed.
    destruct π;destruct t0;destruct t;try tauto;intuition.
    (* identical sub-cases *)
    * (* cbv_update above *)
      { rewrite orl_map in strict.
        destruct strict as (x & inlist & intree).
        apply H with (p:=x);auto.
        - apply andl_in_map with (l:=lp);trivial.
        - apply cache_path_transitivity_left with (c:=c1) (c':=c) (l:=lp);auto.
          intros;apply (left_bound_to_right_bound qic qif cs);trivial.
          apply andl_in_map with (l:=lp);trivial.
      }
    * (* cbv_read above *)
      { rewrite orl_map in strict.
        destruct strict as (x & inlist & intree).
        apply H with (p:=x);auto.
        - apply andl_in_map with (l:=lp);trivial.
        - apply cache_path_transitivity_left with (c:=c1) (c':=c) (l:=lp);auto.
          intros;apply (left_bound_to_right_bound qic qif cs);trivial.
          apply andl_in_map with (l:=lp);trivial.
      }
- (* cbv_update *)
  simpl in well_formed.
  destruct t;try tauto.
  simpl in cache.
  destruct well_formed as (_ & _ & _ & _ & _ & _ & _ & _ & cl & _ & _ & wf_ind & _).
  simpl in subtree.
  destruct subtree as [equal | strict].
  + subst pi;simpl;tauto.
  + apply IHπ;auto.
    rewrite cl;trivial.
- (* cbv_read *)
  simpl in subtree.
  destruct subtree as [equal | impossible];try tauto.
  subst pi;simpl;trivial.
Qed.

Definition judgsize (p:cbv) := (╎proj_left p╎ + value_size (proj_right p))%nat.

Lemma qi_active_bounded_by_size qic qif cs: forall f lval lt,
  valid_QI qic qif cs ->
  let t :=  (fapply f lt) in
  let l := (map (fun x=> Qpos_mult mcs (Qpos_of_nat (╎t╎))) lt) in
  lt = map term_from_value lval ->
  term_assignment qic qif t <= (qif f l).
Proof.
intros f lval lt valid.
unfold valid_QI in valid.
destruct valid as (additivity & max_cs & non_zero & sub & mono & compat).
intros.
apply Qle_trans with (y:=qif f (map (fun v => Qpos_mult mcs (Qpos_of_nat (╎v╎))) lt)).
apply Qle_trans with (y:=qif f (map (term_assignment qic qif) lt)).
- simpl;auto with *.
- apply mono.
  subst lt.
  rewrite map_map;rewrite map_map.
  apply Forall2_map.
  intros.
  rewrite compatible_sizes.
  rewrite value_as_term_assignment.
  apply (QI_le_value_size qic cs);trivial.
- unfold l.
  apply mono.
  apply Forall2_map.
  intros.
  unfold Qpos_mult, Qposle.
  simpl.
  eapply Qle_trans; rewrite Qmult_comm;
  [apply Qle_refl| apply Qmult_le_compat_r];
  [| destruct mcs; trivial].
  rewrite <- Zle_Qle.
  rewrite Zpos_P_of_succ_nat.
  etransitivity; [|apply Z.le_succ_diag_r].
  apply inj_le.
  apply le_trans with (m:=suml (map (term_size (constructor:=constructor)) lt)).
  apply le_trans with (m:=maxl (map (term_size (constructor:=constructor)) lt)).
  + apply maxl_is_max.
    apply in_map;trivial.
  + apply maxl_le_suml.
  + auto with *.
Qed.

(** Theorem 8 *)
Lemma active_size_bound qic qif cs: forall i sub p c f lv d v, forall pi,
  valid_QI qic qif cs ->
  let t :=  (fapply f lv) in
  let π := cbv_update i sub p c t d v in
  let l:= (map (fun x=> Qpos_mult mcs (Qpos_of_nat (╎t╎))) lv) in
  wf π -> In pi (ℐᵃ π) -> cache_bounded qic qif c ->
  Qpos_of_nat (judgsize pi) <= Qpos_mult (Qpos_of_nat(max_arity + 1)) (qif f l) + 1.
Proof.
intros i sub p c f lv d v pi valid t π l well_formed active cache.
unfold valid_QI in valid;destruct valid as (additivity & max_cs & non_zero & subt & mono & compat).
assert (InCBV pi π) as subtree.
apply ℐᵃ_inCBV;trivial.
assert (wf pi) as sub_wf.
apply wf_InCBV_wf with (π:=π);trivial.
apply activation_is_function in active.
destruct active as (i' & sub' & p' & c1 & t0 & c2 & v0 & pi_is_upd).
destruct pi;try discriminate pi_is_upd.
simpl.
simpl in sub_wf;destruct t1;try tauto.
destruct sub_wf as (_ & lp & _ & _ & _ & Hl0 & _ & _ & _ & _ & _ & _ & arity).
set (s:=fapply f0 l0);set (u:=v2).

apply Qle_trans with (y:=(Qpos_of_nat(max_arity)+1) * (term_assignment qic qif (fapply f lv)) + 1).
apply Qle_trans with (y:=(Qpos_of_nat(max_arity)+1)*(term_assignment qic qif s) + 1).
apply Qle_trans with (y:=(Qpos_of_nat(length l0))*(term_assignment qic qif s) + (term_assignment qic qif s) + 1).
apply Qle_trans with (y:=qsuml (map (fun t => term_assignment qic qif s) l0) + (term_assignment qic qif s) + 1).
apply Qle_trans with (y:=qsuml (map (term_assignment qic qif) l0) + (term_assignment qic qif s) + 1).
apply Qle_trans with (y:= Qpos_of_nat(suml (map (@term_size _ _ _) l0)) + (term_assignment qic qif s) + 1).
apply Qle_trans with (y:=Qpos_of_nat (╎s╎) + (term_assignment qic qif s)).
apply Qle_trans with (y:=Qpos_of_nat (╎s╎) + (value_assignment qic u)).
apply Qle_trans with (y:=Qpos_of_nat (╎s╎ + value_size u)).

- auto with *.
- rewrite Qpos_of_nat_plus_compat.
  simpl.
  rewrite Zpos_P_of_succ_nat.
  rewrite <- Nat2Z.inj_succ.
  apply Qplus_le_compat; auto with *.
  apply (value_size_le_QI qic cs);auto.
- apply Qplus_le_compat; auto with *.
  apply (left_bound_to_right_bound qic qif cs) with (pi:=cbv_update n v1 pi c0 s c3 u);trivial.
  + unfold valid_QI;tauto.
  + apply wf_InCBV_wf with (π:=π);trivial.
  + apply (cache_left_bounded_global qic qif cs) with (π:=π);auto.
    unfold valid_QI;tauto.
- simpl; rewrite Zpos_P_of_succ_nat.
  unfold Z.succ.
  rewrite inject_Z_plus.
  ring_simplify.
  auto with *.
- apply Qplus_le_compat; auto with *.
  apply Qplus_le_compat; auto with *.
  subst l0.
  rewrite qsuml_suml.
  repeat rewrite map_map.
  apply qsuml_map_le;intros x H.
  rewrite compatible_sizes.
  rewrite value_as_term_assignment.
  apply (value_size_le_QI qic cs);trivial.
- apply Qplus_le_compat; auto with *.
  apply Qplus_le_compat; auto with *.
  apply qsuml_map_le;intros.
  unfold s;simpl.
  apply subt.
  apply in_map;trivial.
- apply Qplus_le_compat; auto with *.
  apply Qplus_le_compat; auto with *.
  rewrite Qmult_comm, qsuml_map_const.
  auto with *.
- apply Qplus_le_compat; auto with *.
  ring_simplify.
  apply Qplus_le_compat; auto with *.
  rewrite Qmult_comm at 1.
  eapply Qle_trans; rewrite Qmult_comm;
  [apply Qle_refl| apply Qmult_le_compat_r]; auto with *.
  + unfold Qpos_of_nat; simpl.
    rewrite <- Zle_Qle.
    apply inj_le; trivial.
  + destruct term_assignment.
    auto with *.
- apply Qplus_le_compat; auto with *.
  apply Qmult_le_l; auto with *.
  + rewrite Qplus_comm.
    eapply Qle_lt_trans with (y := 0 + 0); [auto with * |].
    apply Qplus_lt_le_compat; auto with *.
    destruct (Qpos_of_nat max_arity); trivial.
  + apply (QI_never_increase_global qic qif cs) with 
      (pi:=cbv_update n v1 pi c0 s c3 u) (π:=π);auto.
  unfold valid_QI;tauto.
- apply Qplus_le_compat; auto with *.
  unfold Qpos_of_nat; simpl.
  rewrite Nat2Z.inj_add; simpl.
  rewrite inject_Z_plus; simpl.
  unfold inject_Z.
  apply Qmult_le_l; auto with *.
  + unfold Qplus, Qlt; simpl; omega.
  + unfold π in *;clear π.
    unfold t in *;clear t.
    simpl in well_formed.
    destruct well_formed as (_ & lp0 & t' & _ & _ & Hlv & _ & _ & _ & _ & _ & wfp & _).
    apply (qi_active_bounded_by_size qic qif cs) with (lval:=map (psubst sub) lp0) (lt:=lv);auto.
    unfold valid_QI;tauto.
Qed.

Lemma active_size_bound_max qic qif cs: forall i s p c f lv d v,
  valid_QI qic qif cs ->
  let t :=  (fapply f lv) in
  let pi := cbv_update i s p c t d v in
  let la := (ℐᵃ pi)  in
  let l:= (map (fun x=> Qpos_mult mcs (Qpos_of_nat (╎t╎))) lv) in
  wf pi -> cache_bounded qic qif c -> forall la', incl la' la -> 
  Qpos_of_nat(maxl (map judgsize la')) <= Qpos_plus (Qpos_mult(Qpos_of_nat(max_arity + 1)) (qif f l)) 1%nat.
Proof.
intros i s p c f lv d v valid t pi la l Hwf Hcb la' Hsslist.
induction la'.
- simpl; rewrite Nat2Z.inj_add, inject_Z_plus; simpl; unfold inject_Z.
  eapply Qle_trans with (y := 0 + 0); [ ring_simplify; auto with *|].
  apply Qplus_le_compat; auto with *.
  apply Qmult_le_0_compat.
  + unfold Qle, Qplus; simpl; omega.
  + apply Qpos_pos.
- simpl map.
  simpl maxl.
  rewrite Qpos_of_nat_max.
  apply qmax_lub.
  + apply (active_size_bound qic qif cs i s p c f lv d v a);auto with *.
  + apply IHla'; apply tl_incl with (a:=a);trivial.
Qed.

Lemma 𝓢_sublist: forall c c' lp lp',
  andl (map wf lp) -> cache_path c c' lp = true -> incl lp' lp ->
  (forall p : cbv, In p lp -> wf p ->
   (𝓢 p <= maxl (map judgsize (ℐᵃ p)))%nat) ->
   (maxl (map (@𝓢 _ _ _) lp') <=
   maxl (map judgsize (flat_map (ℐᵃ (constructor:=constructor)) lp')))%nat.
Proof.
induction lp'.
- (* induction: nil *)
  simpl;intros;auto.
- (* induction: cons *)
  intros.
  simpl.
  rewrite map_app.
  rewrite maxl_app.
  apply Nat.max_le_compat.
  + (* left case of max_le_compat *)
    apply (H2 a).
    unfold incl in H1;apply H1;simpl;auto.
    apply andl_in_map with (l:=lp);auto.
    unfold incl in H1;apply (H1 a);simpl;auto.
  + (* right case of max_le_compat *)
    apply IHlp';intros;auto.
    apply tl_incl with (a:=a);trivial.
Qed.

Lemma 𝓢_is_max: forall pi,
   let S := 𝓢 pi in
   wf pi -> (S <= maxl (map judgsize (ℐᵃ pi)))%nat.
Proof.
induction pi using cbv_ind2;intros;auto.
- (* cbv_constr *)
  unfold S;simpl.
  simpl in H0;destruct t;destruct v;try tauto.
  destruct H0 as (cpath & Hc & HGl & Hl0 & wf_list & arity).
  apply 𝓢_sublist with (c:=c1) (c':=c2) (lp:=lp);auto.
  apply incl_refl.
- (* cbv_split *)
  unfold S;simpl.
  rewrite map_app.
  rewrite maxl_app.
  apply Nat.max_le_compat.
  + apply IHpi.
    simpl in H0.
    destruct pi;destruct t0;destruct t;tauto.
  + simpl in H0;destruct pi;destruct t0;destruct t;try tauto;
          destruct H0 as (Hc & cpath & Hl0 & Hl & wf_list & Hf & Hv & wfp & arity);
          apply 𝓢_sublist with (c:=c1) (c':=c) (lp:=lp);auto;apply incl_refl.
- (* cbv_update *)
  simpl ℐᵃ.
  rewrite map_cons.
  simpl maxl.
  simpl in S.
  apply Nat.max_le_compat;auto.
  apply IHpi.
  simpl in H.
  destruct t;try tauto.
  destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _);trivial.
Qed.

Theorem 𝓢_bound qic qif cs: forall i s p c f lv d v,
  valid_QI qic qif cs ->
  let t :=  (fapply f lv) in
  let π := cbv_update i s p c t d v in
  let l:= (map (fun x=> Qpos_mult mcs (Qpos_of_nat (╎t╎))) lv) in
  let S := 𝓢 π in
  wf π -> cache_bounded qic qif c ->
  Qpos_of_nat S <= Qpos_plus (Qpos_mult (max_arity + 1)%nat (qif f l)) 1%nat.
Proof.
intros i s p c f lv d v valid;intros.
generalize (𝓢_is_max π H).
unfold S, π,t.
intros.
apply Qle_trans with (y:= Qpos_of_nat(maxl (map judgsize (ℐᵃ π))));auto.
- simpl.
  rewrite <- Zle_Qle.
  apply inj_le; trivial.
- apply (active_size_bound_max qic qif cs i s p c f lv d v);auto.
  apply incl_refl.
Qed.

(* partial version of compatible QI *)

Definition p_assignment_function := function -> option(list Qpos -> Qpos).

(* partial assignment of a term*)
Fixpoint p_term_assignment (qic:assignment_constructor) (qif:p_assignment_function)
(t:term) {struct t} : option Qpos:=
   match t with
  | var v => Some (exist _ 0 Lib.qmaxl_obligation_1)
  | capply c lt => option_map (qic c) (option_list_map(map (p_term_assignment qic qif) lt))
  | fapply f lt=> option_bind (fun g => option_map g (option_list_map(map (p_term_assignment qic qif)  lt)))
                              (qif f)
end.

Definition complete_p_QI (qif : p_assignment_function) f :=
  complete_option qsuml (qif f).

Lemma p_term_assignment_term_assignment qic qif t v:
  p_term_assignment qic qif t = Some v ->
  term_assignment qic (complete_p_QI qif) t = v.
Proof.
revert v; induction t using term_ind2.
- intros n H; now inversion H.
- unfold option_map; intros v H0; simpl p_term_assignment in H0.
  simpl term_assignment.
  case_eq (option_list_map (map (p_term_assignment qic qif) l));
    [| intro H1; rewrite H1 in H0; inversion H0].
  intros lv Hlv.
  rewrite option_list_map_map with (f := complete_option (exist _ 0 Lib.qmaxl_obligation_1)) in H0.
  + simpl option_map in H0; inversion H0.
    rewrite map_map; f_equal; apply map_ext_in; intros a Ha.
    apply option_list_map_Some with (x := p_term_assignment qic qif a) in Hlv.
    * destruct Hlv as (va & Hva); rewrite Hva; auto.
    * now apply in_map.
  + intros x Hx.
    eapply option_list_map_Some in Hlv; eauto.
    now destruct Hlv as [vx Hvx]; rewrite Hvx.
- unfold option_map, complete_p_QI; intros v H0; simpl p_term_assignment in H0.
  case_eq (qif f); [ | intro Hf; rewrite Hf in H0; inversion H0].
  intros g Hg; rewrite Hg in *; simpl in H0.
  simpl term_assignment.
  case_eq (option_list_map (map (p_term_assignment qic qif) l));
    [| intro H1; rewrite H1 in H0; inversion H0].
  intros lv Hlv.
  rewrite Hg; simpl.
  rewrite Hlv in H0.
  inversion H0.
  subst v.
  f_equal.
  assert(Heq : Some (map
  (term_assignment qic
     (fun f0 : function => complete_option qsuml (qif f0)))
  l) = Some lv); [ | now inversion Heq].
  rewrite <- Hlv.
  erewrite option_list_map_map.
  + rewrite map_map.
    instantiate (1 := complete_option (exist _ 0 Lib.qmaxl_obligation_1)).
    f_equal.
    apply map_ext_in.
    intros a Ha.
    apply option_list_map_Some with (x := p_term_assignment qic qif a) in Hlv.
    * destruct Hlv as (va & Hva); rewrite Hva; auto.
    * now apply in_map.
  + intros x Hx.
    eapply option_list_map_Some in Hlv; eauto.
    now destruct Hlv as [vx Hvx]; rewrite Hvx.
Qed.

Notation "x ≤p y" := (option_rel Qposle x y) (at level 60).

Definition p_compatible_QI qic qif:= forall f lp t, forall s:variable -> value,
  let ru := rule_intro f lp t in
  (In ru prog) ->
    p_term_assignment qic qif (subst s t) ≤p
    p_term_assignment qic qif (subst s (lhs_of_rule ru)).

Lemma p_compatible_compatible qic:
  {pqif | p_compatible_QI qic pqif} -> {qif | compatible_QI qic qif}.
Proof.
unfold compatible_QI, p_compatible_QI.
intros [qif H]; exists (complete_p_QI qif).
intros f lp t s Hr.
assert (H' := H f lp t s Hr).
destruct H' as (v1 & v2 & Hv1 & Hv2 & Heq).
apply p_term_assignment_term_assignment in Hv1.
apply p_term_assignment_term_assignment in Hv2.
now subst.
Qed.

Lemma p_term_assignment_ext qic f f':
 (forall x, f x = f' x) ->
 forall t, p_term_assignment qic f t= p_term_assignment qic f' t.
Proof.
intro Heq.
induction t using term_ind2.
- trivial.
- simpl p_term_assignment; f_equal; f_equal; now apply map_ext_in.
- simpl p_term_assignment.
  rewrite <- Heq.
  destruct (f f0) as [v |]; trivial.
  simpl; f_equal; f_equal; now apply map_ext_in.
Qed.

Lemma p_compatible_QI_ext qic f f':
 (forall x, f x = f' x) ->
 p_compatible_QI qic f ->
 p_compatible_QI qic f'.
Proof.
intros Heq Hf; unfold p_compatible_QI in *.
intros;
do 2(rewrite <- p_term_assignment_ext with (f := f) (f' := f'); trivial).
auto.
Qed.

Lemma p_compatible_QI_split qic f h:
  {g | p_compatible_QI qic (f;;h;;g)} -> {g | p_compatible_QI qic (f;;g)}.
Proof.
- intro H.
destruct H as (g & Hhg).
exists (h;;g); eapply p_compatible_QI_ext; [ | exact Hhg].
intro; now rewrite option_choice_assoc.
Qed.

Lemma p_term_assignment_first_choice qic f t v:
  p_term_assignment qic f t = Some v ->
  forall g, p_term_assignment qic (f;;g) t = Some v.
Proof.
revert v.
induction t using term_ind2.
- intros; assumption.
- intros v Hv g; simpl in *.
  rewrite <- Hv; do 2 f_equal.
  apply map_ext_in; intros a Ha.
  apply option_map_Some in Hv; destruct Hv as (v' & Hv').
  apply option_list_map_Some with (x := p_term_assignment qic f a) in Hv';
  [ | now apply in_map].
  destruct Hv' as (v'' & Hv''); rewrite Hv''.
  apply H; assumption.
- intros v Hv g; simpl in *.
  rewrite <- Hv.
  simpl option_choice.
  case_eq (f f0); [| intro Hnone; rewrite Hnone in Hv; inversion Hv].
  intros v' Hv'.
  assert (Hfg : (f;; g) f0 = Some v') by
    (unfold option_choice; now rewrite Hv').
  rewrite Hfg.
  simpl.
  do 2 f_equal.
  apply map_ext_in.
  intros a Ha.
  apply option_bind_Some in Hv.
  destruct Hv as (v'' & _ & Hv).
  apply option_map_Some in Hv.
  destruct Hv as (v'''' & Hv).
  apply option_list_map_Some with (x := p_term_assignment qic f a) in Hv.
  + destruct Hv as (lv & Hlv).
    erewrite H; eauto.
  + now apply in_map.
Qed.

Lemma value_as_p_term_assignment qic qif: forall v:value,
  (p_term_assignment qic qif (term_from_value v)) = Some (value_assignment qic v).
Proof.
induction v using value_ind2.
simpl.
unfold option_map, option_list_map.
rewrite map_map.
rewrite option_list_map_map with
  (f := fun x => match x with Some v => v | None => (exist _ 0 Lib.qmaxl_obligation_1) end).
- do 2 f_equal; rewrite map_map; apply map_ext_in.
  intros; rewrite H; trivial.
- intros x Hx.
  apply in_map_iff in Hx.
  destruct Hx as (n & Hn1 & Hn2).
  rewrite H in Hn1; trivial.
  rewrite <- Hn1; trivial.
Qed.

Definition p_subterm (qif : p_assignment_function) : Prop :=
forall (f : function) (l : list Qpos) (x : Qpos), x ∈ l ->
  match qif f with
  | None => True
  | Some f0 => (x <= f0 l)
  end.

Definition p_monotonicity (qif : p_assignment_function) : Prop :=
  forall (f : function) (lx ly : list Qpos),
    Forall2 Qposle lx ly ->
    match qif f with
    | None => True
    | Some f0 => f0 lx <= f0 ly
    end.

Definition p_smc qic (qif : p_assignment_function) : Prop :=
 p_subterm qif /\ p_monotonicity qif /\ p_compatible_QI qic qif.

Lemma p_smc_split f h qic:
  {g | p_smc qic (f;;h;;g)} -> {g | p_smc qic (f;;g)}.
Proof.
intro H.
unfold p_smc in *.
destruct H as (g & Hhgs & Hhgm & Hhgc).
exists (h;;g).
unfold p_subterm, p_monotonicity, p_compatible_QI in *.
repeat split; intros f0 l x Hin.
- assert (H := Hhgs f0 l x Hin); now rewrite <- option_choice_assoc in H.
- assert (H := Hhgm f0 l x Hin); now rewrite <- option_choice_assoc in H.
- eapply p_compatible_QI_ext; [ | exact Hhgc]; intro; now rewrite option_choice_assoc.
Qed.

Lemma p_smc_smc qic :
  {pqif | p_smc qic ((fun _ => None);; pqif)} ->
  {qif | subterm qif /\ monotonicity_qif qif /\ compatible_QI qic qif}.
Proof.
unfold p_smc, compatible_QI, p_compatible_QI, p_subterm, subterm,
       monotonicity_qif, p_monotonicity.
intros (qif & Hs & Hm & Hc); exists (complete_p_QI qif).
repeat split.
- intros f l x Hin.
  assert (H' := Hs f l x Hin).
  unfold complete_p_QI, complete_option.
  unfold option_choice in H'.
  destruct (qif f); trivial.
  now apply in_le_qsuml.
- intros f l x Hin.
  assert (H' := Hm f l x Hin).
  unfold complete_p_QI, complete_option.
  unfold option_choice in H'.
  destruct (qif f); trivial.
  revert x Hin.
  induction l; intros x Hin; simpl.
  + destruct qsuml; trivial.
  + inversion Hin as [Ha Hin|]; subst.
    simpl.
    apply Qplus_le_compat; auto with *.
- intros f lp t s Hr.
  assert (H' := Hc f lp t s Hr).
  destruct H' as (v1 & v2 & Hv1 & Hv2 & Heq).
  apply p_term_assignment_term_assignment in Hv1.
  apply p_term_assignment_term_assignment in Hv2.
  now subst.
Qed.

End QI.

Section Partial_QI.

Variables variable function constructor : Type.

Notation p_compatible_QI := (p_compatible_QI variable function constructor).
Notation term_from_value := (Syntax.term_from_value variable function (constructor:=constructor)).
Notation p_smc := (p_smc variable function constructor).

(* f is the current partial qi, and g is what remains to be defined *)
Lemma p_compatible_QI_app f prog1 prog2 qic:
  p_compatible_QI prog1 qic f ->
  {g | p_compatible_QI prog2 qic (f;;g)} ->
  {g | p_compatible_QI (prog1 ++ prog2) qic (f;;g)}.
Proof.
intros Hf [g Hg]; exists g.
unfold p_compatible_QI; intros f0 lp t s Hrule.
apply in_app_iff in Hrule; destruct Hrule as [Hr1 | Hr2]; auto.
eapply (Hf f0 lp t s) in Hr1.
destruct Hr1 as (v1 & v2 & Hv1 & Hv2 & Heq);
exists v1; exists v2; intuition;
now apply p_term_assignment_first_choice.
Qed.

Lemma p_smc_QI_app f prog1 prog2 qic:
  p_compatible_QI prog1 qic f ->
  {g | p_smc prog2 qic (f;;g)} ->
  {g | p_smc (prog1 ++ prog2) qic (f;;g)}.
Proof.
unfold p_smc.
intros Hfc (g & Hs & Hm & Hc); exists g; repeat split.
- unfold p_subterm in *; intros h l x Hin.
  assert (H' := Hs h l x Hin).
  unfold option_choice in *; destruct (f h); trivial.
- unfold p_monotonicity in *; intros h l x Hin.
  assert (H' := Hm h l x Hin).
  unfold option_choice in *; destruct (f h); trivial.
- intros f0 lp t s r Hrule.
  apply in_app_iff in Hrule; destruct Hrule as [Hr1 | Hr2].
  + eapply (Hfc f0 lp t s) in Hr1.
    destruct Hr1 as (v1 & v2 & Hv1 & Hv2 & Heq);
    exists v1; exists v2; intuition;
    now apply p_term_assignment_first_choice.
  + now apply Hc.
Qed.

End Partial_QI.
