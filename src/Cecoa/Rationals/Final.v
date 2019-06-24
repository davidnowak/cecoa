Require Import QArith Le Max List Bool NPeano Omega Psatz.
Require Import Cecoa.Rationals.Lib Cecoa.Rationals.Syntax Cecoa.Rationals.CBV_cache Cecoa.Rationals.Bounds Cecoa.Rationals.Ordering Cecoa.Rationals.QI.

Section Main.

(* Syntax *)

Variables variable function constructor : Type.
Notation value := (Syntax.value constructor).
Notation term := (Syntax.term variable function constructor).
Notation pattern := (Syntax.pattern variable constructor).
Notation rule := (Syntax.rule variable function constructor).
Notation "'╎' t '╎'" := (@term_size variable function constructor t) (at level 10).

Variable prog : list rule.
Variable max_arity:nat.
Variable rule_default : rule.

Hypothesis prog_is_wf: wf_prog max_arity prog.

Variable variable_eq_dec : forall (x1 x2 : variable), {x1=x2}+{x1<>x2}.
Variable function_eq_dec : forall (x1 x2 : function), {x1=x2}+{x1<>x2}.
Variable constructor_eq_dec : forall (x1 x2 : constructor), {x1=x2}+{x1<>x2}.

Notation cache := (CBV_cache.cache variable function constructor).
Notation cbv := (CBV_cache.cbv variable function constructor).
Notation wf := (CBV_cache.wf variable_eq_dec function_eq_dec constructor_eq_dec rule_default
                prog max_arity).
Notation "'∣' p '∣'" := (@size variable function constructor p) (at level 10).

(* PPO *)
Variable rank: function -> nat.
Variable max_rank : nat.
Hypothesis pos_max_rank : 0 < max_rank.
Hypothesis max_rank_is_max_rank : forall f, rank f <= max_rank.
Hypothesis prog_is_ppo : PPO_prog prog rank.

Definition gsp := (Bounds.gary_seven_poly variable function constructor prog max_rank).
Definition bep := (Bounds.bobby_eight_poly variable function constructor max_arity prog).

(* QI *)
Variable cs: constructor -> Qpos.  (* constructor size *)
Variable mcs: Qpos. (* max constructor size *)
Variable qic: assignment_constructor constructor.
Variable qif: assignment_function function.
Hypothesis prog_has_QI: valid_QI variable function constructor prog mcs qic qif cs.
Notation cache_bounded := (QI.cache_bounded variable function constructor qic qif).

Definition CBV_bound A S C :=  (* generic bound *)
  (* A : number of ℐᵃ
     S : max size of an activation
     C : cache *)
  (A * 𝓡 prog S + A + 1 + (max_arity * A * (1 + 𝓡 prog S))) *
  (𝓡 prog S + S + cache_size C +
  (1 + max S (maxl (map (fun tv : term * value => value_size (snd tv)) C))) *
  (1 + (A * 𝓡 prog S + A) + max_arity * (A * 𝓡 prog S + A))) +
  cache_size C.

Definition PPO_bound S := gsp (bep S).
(* S : max size of an activation *)

(* Rough upper bound on rationals *)
Definition ub (q :  Q) : nat := let (n,d):= q in Z.abs_nat n.

Lemma ub_is_ub : forall q, (q <= inject_Z (Z.of_nat (ub q)))%Q.
Proof.
intros (q&d). simpl. destruct q; unfold inject_Z; simpl; auto with *;
rewrite positive_nat_Z; unfold Qle; simpl; nia.
Qed.

Definition QI_bound (f:function) (lv: list term) := 
  (* f : active function symbol
     lv : list of its arguments *)
    (Qpos_of_nat(max_arity + 1)) *q
    (qif f (map (fun x=> Qpos_mult mcs (Qpos_of_nat (╎fapply f lv╎))) lv))
    +q 1.

Definition global_bound f lv C :=
  let S:= ub (QI_bound f lv) in
  let A:= PPO_bound S in
  CBV_bound A S C.

(********** Proofs **********)

(* All bounds are increasing *)
Lemma gary_increase: (* move to Ordering ? *)
  forall x y, x <=y -> gsp x <= gsp y.
Proof.
intros.
unfold gary_seven_poly.
apply suml_map_le.
intros.
unfold ℐᵃ_at_rank_bound.
apply Mult.mult_le_compat_l.
apply pow_le_compat;trivial.
Qed.

Lemma PPO_bound_increase:
  (forall x y, x <= y -> PPO_bound x <= PPO_bound y)%nat.
Proof.
intros.
unfold PPO_bound.
apply gary_increase.
apply bobby_increase.
trivial.
Qed.

Lemma 𝓡_increase:
  forall x y, x <= y -> 𝓡 prog x <= 𝓡 prog y.
Proof.
intros.
unfold 𝓡.
apply Mult.mult_le_compat_l.
apply Plus.plus_le_compat_l;trivial.
Qed.

Lemma CBV_bound_increase:
  forall x1 y1 x2 y2 C, x1 <= y1 -> x2 <= y2 -> CBV_bound x1 x2 C <= CBV_bound y1 y2 C.
Proof.
intros.
unfold CBV_bound.
apply Plus.plus_le_compat_r.
apply Mult.mult_le_compat;
repeat (try apply Plus.plus_le_compat; trivial; try apply Mult.mult_le_compat; trivial).
apply Nat.max_le_compat_r;trivial.
Qed.

(** Theorem 9 (P-criterion) *)
Theorem P_criterion: forall i s p c f lv d v,
  let t :=  (fapply f lv) in
  let π := cbv_update i s p c t d v in
  wf π -> cache_bounded c ->
  ∣π∣ <= global_bound f lv c.
Proof.
intros i s p c f lv d v t π well_formed cache_bound.
unfold global_bound.
assert (𝓢 π <= ub (QI_bound f lv)).
- rewrite Nat2Z.inj_le, Zle_Qle.
  eapply Qle_trans; [ | apply ub_is_ub].
  apply 𝓢_bound
 with (prog:=prog) (rule_default:=rule_default)
        (variable_eq_dec:=variable_eq_dec) (function_eq_dec :=function_eq_dec) (constructor_eq_dec:=constructor_eq_dec)
        (qic:=qic) (cs:=cs);trivial.
- apply le_trans with (m:= CBV_bound (PPO_bound (𝓢 π)) (𝓢 π) c).
  + assert (length (ℐᵃ π) <= PPO_bound (𝓢 π)).
    * {
        apply le_trans with (m:=gsp (A_T variable function constructor rank π)).
        - apply gary_seven with (variable_eq_dec:=variable_eq_dec) (function_eq_dec:=function_eq_dec)
                                (constructor_eq_dec:=constructor_eq_dec) (rule_default:=rule_default)
                                (max_arity:=max_arity);try trivial.
          apply PPO_is_compatible_prog;trivial.
        - unfold PPO_bound.
          apply gary_increase.
          apply A_T_bound with (variable_eq_dec:=variable_eq_dec) (function_eq_dec:=function_eq_dec)
                               (constructor_eq_dec:=constructor_eq_dec) (rule_default:=rule_default)
                               (max_rank:=max_rank);trivial.
      }
    * {
        apply le_trans with (m:=CBV_bound (length (ℐᵃ π)) (𝓢 π) c).
        - apply size_bound_gen with (variable_eq_dec:=variable_eq_dec) (function_eq_dec:=function_eq_dec)
                                    (constructor_eq_dec:=constructor_eq_dec) (rule_default:=rule_default);trivial.
        - apply CBV_bound_increase;trivial.
      }
  + apply CBV_bound_increase;try trivial.
    * apply PPO_bound_increase;try trivial.
Qed.

End Main.
