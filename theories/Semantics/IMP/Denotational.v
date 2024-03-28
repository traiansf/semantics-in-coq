From stdpp Require Import prelude.

From sets Require Import Ensemble.

From Semantics.IMP Require Import Syntax State Eval BigStep.

Section sec_denotational.

Context `{EqDecision L}.

Definition denota (a : AExp L) : State L -> Z :=
    fun sigma => aeval sigma a.

Definition denotb (b : BExp L) : State L -> bool :=
    fun sigma => beval sigma b.

Inductive delta : Ensemble (State L * State L) :=
| delta_intro : forall (sigma : State L), delta (sigma, sigma).

Lemma elem_of_delta: forall (sigma sigma' : State L),
    (sigma, sigma') ∈ delta <-> sigma = sigma'.
Proof. by split; [inversion 1 | intros ->; constructor]. Qed.

Inductive denot_asgn (x : L) (Ra : State L -> Z) : Ensemble (State L * State L) :=
| dasgn_intro : forall sigma : State L,
    denot_asgn x Ra (sigma, update sigma x (Ra sigma)).

Inductive fwd_relation_composition
    (R Q : Ensemble (State L * State L)) : Ensemble (State L * State L) :=
| relation_composition_intro : forall a b c : State L,
    (a, b) ∈ R -> (b, c) ∈ Q -> fwd_relation_composition R Q (a, c).

Lemma elem_of_fwd_relation_composition:
    forall (R Q : Ensemble (State L * State L)) (sigma sigma' : State L),
    (sigma, sigma') ∈ fwd_relation_composition R Q
      <->
    exists (sigma'' : State L), (sigma, sigma'') ∈ R /\ (sigma'', sigma') ∈ Q.
Proof.
    intros; split.
    - by inversion 1; subst; eexists; split.
    - by intros (? & ? & ?); econstructor.
Qed.

Inductive relation_selector (cond : State L -> bool)
    (Then Else : Ensemble (State L * State L)) : Ensemble (State L * State L) :=
| relation_selector_then : forall (sigma sigma' : State L), cond sigma = true ->
    (sigma, sigma') ∈ Then -> relation_selector cond Then Else (sigma, sigma')
| relation_selector_else : forall (sigma sigma' : State L), cond sigma = false ->
    (sigma, sigma') ∈ Else -> relation_selector cond Then Else (sigma, sigma')
.

Lemma elem_of_relation_selector:
    forall (cond : State L -> bool) (Then Else : Ensemble (State L * State L))
        (sigma sigma' : State L),
    (sigma, sigma') ∈ relation_selector cond Then Else
      <->
    (cond sigma = true /\ (sigma, sigma') ∈ Then)
      \/
    (cond sigma = false /\ (sigma, sigma') ∈ Else).
Proof.
    split.
    - by inversion 1; subst; [left | right].
    - intros [[]|[]].
      + by apply relation_selector_then.
      + by apply relation_selector_else.
Qed.

Definition while_step (cond : State L -> bool)
    (body while: Ensemble (State L * State L)) : Ensemble (State L * State L) :=
    relation_selector cond (fwd_relation_composition body while) delta.

Lemma elem_of_while_step (cond : State L -> bool)
    (body while: Ensemble (State L * State L)):
    forall (sigma sigma' : State L),
    (sigma, sigma') ∈ while_step cond body while
      <->
    (cond sigma = false /\ sigma = sigma')
      \/
    (cond sigma = true /\ exists (sigma'' : State L), (sigma, sigma'') ∈ body /\ (sigma'', sigma') ∈ while).
Proof.
    intros; unfold while_step.
    rewrite elem_of_relation_selector, elem_of_delta, elem_of_fwd_relation_composition.
    by split; intros [|]; [right | left | right | left].
Qed.


#[export] Instance while_step_proper (cond : State L -> bool)
    (body : Ensemble (State L * State L)) : Proper ((⊆) ==> (⊆)) (while_step cond body).
Proof.
    intros  W1 W2 Hsub (sigma, sigma') Hin.
    destruct (cond sigma) eqn:Hcond.
    - inversion Hin; subst; [| by rewrite Hcond in *; discriminate].
      inversion H2; subst.
      apply relation_selector_then; [done |].
      econstructor; [done |].
      by apply Hsub.
    - inversion Hin; subst; [by rewrite Hcond in *; discriminate |].
      by apply relation_selector_else.
Qed.

Fixpoint denotc (c : Cmd L) : Ensemble (State L * State L) :=
match c with
| Skip => delta
| Asgn x a => denot_asgn x (denota a)
| Seq c0 c1 => fwd_relation_composition (denotc c0) (denotc c1)
| If b c0 c1 => relation_selector (denotb b) (denotc c0) (denotc c1)
| While b c => lfp (while_step (denotb b) (denotc c))
end.

(* For a proof of Knaster-Tarski's theorem, see https://github.com/traiansf/sets-in-coq/blob/main/theories/sets/Ensemble.v#L413 *)

Lemma denot_equiv_big_step : forall (c : Cmd L) (sigma sigma' : State L),
    big_step c sigma sigma' <-> (sigma, sigma') ∈ denotc c.
Proof.
    split.
    - intros [Hbs]; induction Hbs.
      + by constructor.
      + by constructor.
      + by econstructor.
      + by apply relation_selector_then.
      + by apply relation_selector_else.
      + apply knaster_tarski_lfp_fix; [by typeclasses eauto |].
        apply relation_selector_else; [done | by constructor].
      + apply knaster_tarski_lfp_fix; [by typeclasses eauto |].
        apply relation_selector_then; [done | by econstructor].
    - intros Hdenot; revert sigma sigma' Hdenot; induction c; intros.
      + by inversion Hdenot; subst; constructor; constructor.
      + by inversion Hdenot; subst; constructor; constructor.
      + inversion Hdenot; subst.
        apply IHc1 in H1 as [Hc1].
        apply IHc2 in H2 as [Hc2].
        by constructor; econstructor.
      + inversion Hdenot; subst.
        * apply IHc1 in H2 as [Hc1].
          by constructor; eapply bs_if_true.
        * apply IHc2 in H2 as [Hc2].
          by constructor; eapply bs_if_false.
      + pose (W (sp : State L * State L) := big_step (While b c) sp.1 sp.2).
        cut (denotc (While b c) ⊆ W); [by intro Hincl; apply Hincl in Hdenot |].
        clear sigma sigma' Hdenot.
        apply knaster_tarski_least_pre_fixpoint.
        intros (sigma, sigma') Hin.
        inversion Hin; subst.
        * inversion H2; subst.
          apply IHc in H3 as [Hc].
          destruct H4 as [Hw].
          by constructor; eapply bs_while_true.
        * inversion H2; subst.
          by constructor; eapply bs_while_false.
Qed.

Definition partial_function `(R : Ensemble (A * B)) :=
    forall (a : A) (b1 b2 : B), (a, b1) ∈ R -> (a, b2) ∈ R -> b1 = b2.

#[export] Instance partial_function_proper {A B} : Proper ((≡) ==> iff) (@partial_function A B).
Proof.
    by intros R Q Heqv; unfold partial_function; setoid_rewrite Heqv.
Qed.

Lemma pf_empty : forall (A B : Type), @partial_function A B ∅.
Proof. by intros * a b1 b2 Hb2; inversion Hb2. Qed.

Lemma pf_delta : partial_function delta.
Proof.
    intros sigma sigma' sigma'' H' H''.
    by inversion H'; inversion H''; subst.
Qed.

Lemma pf_denot_asgn : forall (x : L) (Ra : State L -> Z),
    partial_function (denot_asgn x Ra).
Proof.
    intros x a sigma sigma' sigma'' H' H''.
    by inversion H'; inversion H''; subst.
Qed.

Lemma pf_fwd_relation_composition: forall (R Q : Ensemble (State L * State L)),
    partial_function R -> partial_function Q ->
    partial_function (fwd_relation_composition R Q).
Proof.
    intros R Q HR HQ sigma sigma' sigma'' H' H''.
    inversion H'; inversion H''; subst.
    rewrite (HR sigma b b0 H1 H5) in *.
    by rewrite (HQ b0 sigma' sigma'' H2 H6).
Qed.

Lemma pf_relation_selector: forall (cond : State L -> bool) (Then Else : Ensemble (State L * State L)),
    partial_function Then -> partial_function Else ->
    partial_function (relation_selector cond Then Else).
Proof.
    intros * HThen HElse sigma sigma' sigma'' H' H''.
    inversion H'; subst.
    - inversion H''; [| by rewrite H1 in *; discriminate].
      by rewrite (HThen sigma sigma' sigma'' H2 H4).
    - inversion H''; [by rewrite H1 in *; discriminate |].
      by rewrite (HElse sigma sigma' sigma'' H2 H4).
Qed.

Lemma pf_while_step: forall (cond : State L -> bool) (body while : Ensemble (State L * State L)),
    partial_function body -> partial_function while ->
    partial_function (while_step cond body while).
Proof.
    by intros; apply pf_relation_selector;
      [apply pf_fwd_relation_composition | apply pf_delta].
Qed.

#[export] Instance while_step_continuous:
    forall (cond : State L -> bool) (body : Ensemble (State L * State L)),
    Continuous (while_step cond body).
Proof.
    intros *; constructor; intros C (sigma, sigma').
    rewrite elem_of_while_step.
    setoid_rewrite elem_of_indexed_union; cbn.
    setoid_rewrite elem_of_while_step.
    split; [intros [[]|[? (sigma'' & Hbody & i & HCi)]] | intros [i [[]|[? (sigma'' & Hbody & HCi)]]]].
    - by exists 0; left.
    - by exists i; right; repeat esplit.
    - by left.
    - by right; repeat esplit.
Qed.

Lemma pf_ascending_chain:
    forall (C : nat -> Ensemble (State L * State L)),
        (forall (n : nat), partial_function (C n)) ->
        ascending_chain C ->
        partial_function (indexed_union C).
Proof.
    intros C Hpf Hchain sigma sigma' sigma''.
    rewrite !elem_of_indexed_union.
    intros [i' Hsigma'] [i'' Hsigma''].
    apply (Hpf (max i' i'') sigma sigma' sigma'').
    - eapply ascending_chain_skipping; [done | | done].
      by lia.
    - eapply ascending_chain_skipping; [done | | done].
      by lia.
Qed.

Lemma pf_denot_while : forall (cond : State L -> bool) (body : Ensemble (State L * State L)),
    partial_function body ->
    partial_function (lfp (while_step cond body)).
Proof.
    intros cond body Hbody.
    rewrite kleene_knaster_tarski_lfp_equiv;
      [| by typeclasses eauto | by apply Omega_continuous_klfp_fixpoint; typeclasses eauto].
    apply pf_ascending_chain; [| by apply kleene_ascending_chain; typeclasses eauto].
    induction n; cbn; [apply pf_empty |].
    by apply pf_while_step.
Qed.

Lemma pf_denotc: forall (c : Cmd L), partial_function (denotc c).
Proof.
    induction c.
    - by apply pf_delta.
    - by apply pf_denot_asgn.
    - by apply pf_fwd_relation_composition.
    - by apply pf_relation_selector.
    - by apply pf_denot_while.
Qed.

End sec_denotational.
