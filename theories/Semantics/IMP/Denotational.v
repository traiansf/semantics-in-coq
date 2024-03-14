From stdpp Require Import prelude.

From sets Require Import Ensemble.

From Semantics Require Import Syntax State Eval BigStep.

Definition denota (a : AExp) : State -> Z :=
    fun sigma => aeval sigma a.

Definition denotb (b : BExp) : State -> bool :=
    fun sigma => beval sigma b.

Inductive delta : Ensemble (State * State) :=
| delta_intro : forall (sigma : State), delta (sigma, sigma).

Inductive denot_asgn (x : nat) (a : AExp) : Ensemble (State * State) :=
| dasgn_intro : forall sigma : State,
    denot_asgn x a (sigma, update sigma x (denota a sigma)).

Inductive fwd_relation_composition
    (R Q : Ensemble (State * State)) : Ensemble (State * State) :=
| relation_composition_intro : forall a b c : State,
    (a, b) ∈ R -> (b, c) ∈ Q -> fwd_relation_composition R Q (a, c).

Inductive relation_selector (cond : State -> bool)
    (Then Else : Ensemble (State * State)) : Ensemble (State * State) :=
| relation_selector_then : forall (sigma sigma' : State), cond sigma = true ->
    (sigma, sigma') ∈ Then -> relation_selector cond Then Else (sigma, sigma')
| relation_selector_else : forall (sigma sigma' : State), cond sigma = false ->
    (sigma, sigma') ∈ Else -> relation_selector cond Then Else (sigma, sigma')
.

Definition while_step (cond : State -> bool)
    (body while: Ensemble (State * State)) : Ensemble (State * State) :=
    relation_selector cond (fwd_relation_composition body while) delta.

#[export] Instance while_step_proper (cond : State -> bool)
    (body : Ensemble (State * State)) : Proper ((⊆) ==> (⊆)) (while_step cond body).
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

Fixpoint denotc (c : Cmd) : Ensemble (State * State) :=
match c with
| Skip => delta
| Asgn x a => denot_asgn x a
| Seq c0 c1 => fwd_relation_composition (denotc c0) (denotc c1)
| If b c0 c1 => relation_selector (denotb b) (denotc c0) (denotc c1)
| While b c => lfp (while_step (denotb b) (denotc c))
end.

(* For a proof of Knaster-Tarski's theorem, see https://github.com/traiansf/sets-in-coq/blob/main/theories/sets/Ensemble.v#L413 *)

Lemma denot_equiv_big_step : forall (c : Cmd) (sigma sigma' : State),
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
      + pose (W (sp : State * State) := big_step (While b c) sp.1 sp.2).
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
