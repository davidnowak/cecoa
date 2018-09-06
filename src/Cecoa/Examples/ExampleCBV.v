Require Import List.
Import List.ListNotations.
Require Import Cecoa.Syntax Cecoa.CBV.

Inductive example_variable : Type := x | y.

Inductive example_function : Type := main | append.

Inductive example_constructor : Type := eps | s0 | s1.

Example example : list (rule example_variable example_function example_constructor) := [
  rule_intro main [p_capply s0 [p_capply s0 [p_var x]]] (fapply append [fapply main [capply s1 [var x]]; fapply main [capply s1 [var x]]]);
  rule_intro main [p_capply s0 [p_capply s1 [p_var x]]] (fapply append [fapply main [capply s1 [var x]]; fapply main [capply s1 [var x]]]);
  rule_intro main [p_capply s1 [p_var x]] (var x);
  rule_intro main [p_capply eps []] (capply eps []);
  rule_intro append [p_capply s0 [p_var x]; p_var y] (capply s0 [fapply append [var x; var y]]);
  rule_intro append [p_capply s1 [p_var x]; p_var y] (capply s1 [fapply append [var x; var y]]);
  rule_intro append [p_capply eps []; p_var y] (var y)
].

Example wf_prog_example : wf_prog 2 example.
Proof.
vm_compute.
split; [ tauto | trivial ].
Qed.

Program Definition example_derivation : {p : cbv example_variable example_function example_constructor | wf example (rule_intro main [] (capply eps [])) p } :=
  let p1 := cbv_constr [] (capply eps []) (c_capply eps []) in
  let p2 := cbv_function 2 (fun _ => c_capply eps []) p1 (fapply main [capply s1 [capply eps []]]) (c_capply eps []) in
  let p3 := cbv_function 6 (fun _ => c_capply eps []) p1 (fapply append [capply eps []; capply eps []]) (c_capply eps []) in
  let p4 := cbv_split [p2; p2] p3 (fapply append [fapply main [capply s1 [capply eps []]]; fapply main [capply s1 [capply eps []]]]) (c_capply eps []) in
  cbv_function 1 (fun _ => c_capply eps []) p4 (fapply main [term_from_value _ _ (c_capply s0 [c_capply s1 [c_capply eps []]])]) (c_capply eps []).

Next Obligation.
simpl; repeat econstructor.
Qed.

(*
Eval simpl in size (projT1 example_derivation).
Eval simpl in max_active_size (projT1 example_derivation).
Eval simpl in activations (projT1 example_derivation).
*)
