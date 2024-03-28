From stdpp Require Import prelude.
From Coq Require Import Classical ClassicalFacts.

From Semantics.IMP Require Import Syntax State Eval.

Section sec_big_step.

Context `{EqDecision L}.

Inductive big_step_proof : Cmd L -> State L -> State L -> Type :=
| bs_skip : forall sigma : State L, big_step_proof Skip sigma sigma
| bs_asgn : forall (x : L) (a : AExp L) (sigma : State L),
    big_step_proof (Asgn x a) sigma (update sigma x (aeval sigma a))
| bs_seq : forall (c0 c1 : Cmd L) (sigma sigma' sigma'' : State L),
    big_step_proof c0 sigma sigma'' ->
    big_step_proof c1 sigma'' sigma' ->
    big_step_proof (Seq c0 c1) sigma sigma'
| bs_if_true : forall (b : BExp L) (c0 c1 : Cmd L) (sigma sigma' : State L),
    beval sigma b = true ->
    big_step_proof c0 sigma sigma' ->
    big_step_proof (If b c0 c1) sigma sigma'
| bs_if_false : forall (b : BExp L) (c0 c1 : Cmd L) (sigma sigma' : State L),
    beval sigma b = false ->
    big_step_proof c1 sigma sigma' ->
    big_step_proof (If b c0 c1) sigma sigma'
| bs_while_false : forall (b : BExp L) (c : Cmd L) (sigma : State L),
    beval sigma b = false ->
    big_step_proof (While b c) sigma sigma
| bs_while_true : forall (b : BExp L) (c : Cmd L) (sigma sigma' sigma'' : State L),
    beval sigma b = true ->
    big_step_proof c sigma sigma'' ->
    big_step_proof (While b c) sigma'' sigma' ->
    big_step_proof (While b c) sigma sigma'
.

Fixpoint bsp_depth `(proof : big_step_proof c sigma sigma') : nat :=
match proof with
| bs_skip _ => 0
| bs_asgn _ _ _ => 0
| bs_seq _ _ _ _ _ bs0 bs1 => 1 + max (bsp_depth bs0) (bsp_depth bs1)
| bs_if_true _ _ _ _ _ _ bs => 1 + (bsp_depth bs)
| bs_if_false _ _ _ _ _ _ bs => 1 + (bsp_depth bs)
| bs_while_false _ _ _ _ => 0
| bs_while_true _ _ _ _ _ _ bsc bsw => 1 + max (bsp_depth bsc) (bsp_depth bsw)
end.

Lemma bsp_while_true_skip_argument :
    forall (sigma0 sigma' : State L) (bs0 : big_step_proof (While (BVal true) Skip) sigma0 sigma'),
    exists (sigma1 : State L) (bs1 : big_step_proof (While (BVal true) Skip) sigma1 sigma'),
    bsp_depth bs1 < bsp_depth bs0.
Proof.
    intros *.
    dependent inversion bs0 as [| | | | | |? ? ? ? sigma1 ? ?  bs1]; subst; [done |].
    exists sigma1, bs1; cbn; lia.
Qed.

Inductive big_step (c : Cmd L) (sigma sigma' : State L) : Prop :=
    big_step_proof_inh : big_step_proof c sigma sigma' -> big_step c sigma sigma'.

Lemma classical_big_step_while_true_skip : forall (sigma sigma' : State L),
    ~ big_step (While (BVal true) Skip) sigma sigma'.
Proof.
    pose (P (n : nat) := exists (sigma sigma' : State L) (Hbs: big_step_proof (While (BVal true) Skip) sigma sigma'), n = bsp_depth Hbs).
    intros sigma sigma' [Hbs].
    assert (HP : P (bsp_depth Hbs)) by (eexists _, _, _; done).
    destruct (excluded_middle_entails_unrestricted_minimization classic P _ HP)
        as [n [(sigman & sigman' & Hbsn & ->) Hminimal]].
    destruct (bsp_while_true_skip_argument _ _ Hbsn) as (statem & Hbsm & Hlt).
    cut (bsp_depth Hbsn <= bsp_depth Hbsm); [by lia |].
    apply Hminimal.
    by eexists _, _, _.
Qed.

Definition bs_equivalence (c0 c1 : Cmd L) : Prop :=
    forall (sigma sigma' : State L),
        big_step c0 sigma sigma' <-> big_step c1 sigma sigma'.

Lemma bs_loop_unrolling: forall (b : BExp L) (c : Cmd L),
    bs_equivalence (While b c) (If b (Seq c (While b c)) Skip).
Proof.
  intros; split; intros [Hw]; inversion Hw; subst; constructor.
  - apply bs_if_false; [done | by constructor].
  - apply bs_if_true; [done | by eapply bs_seq].
  - inversion X; subst.
    by eapply bs_while_true.
  - inversion X; subst.
    by apply bs_while_false.
Qed.

End sec_big_step.