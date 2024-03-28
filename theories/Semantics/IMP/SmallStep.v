From stdpp Require Import prelude.

From Semantics.IMP Require Import Syntax State Eval BigStep.

Section sec_small_step.

Context `{EqDecision L}.

Inductive one_step : relation (Cmd L * State L) :=
| os_asgn : forall (x : L) (a : AExp L) (sigma : State L),
    one_step (Asgn x a, sigma) (Skip, update sigma x (aeval sigma a))
| os_seq : forall (c1 : Cmd L) (sigma : State L),
    one_step (Seq Skip c1, sigma) (c1, sigma)
| os_seq_struct : forall (c0 c0' c1 : Cmd L) (sigma sigma' : State L),
    one_step (c0, sigma) (c0', sigma') ->
    one_step (Seq c0 c1, sigma) (Seq c0' c1, sigma')
| os_if_true : forall (b : BExp L) (c0 c1 : Cmd L) (sigma : State L),
    beval sigma b = true ->
    one_step (If b c0 c1, sigma) (c0, sigma)
| os_if_false : forall (b : BExp L) (c0 c1 : Cmd L) (sigma : State L),
    beval sigma b = false ->
    one_step (If b c0 c1, sigma) (c1, sigma)
| os_while : forall (b : BExp L) (c : Cmd L) (sigma : State L),
    one_step (While b c, sigma) (If b (Seq c (While b c)) Skip, sigma)
.

Definition small_step : relation (Cmd L * State L) := rtc one_step.

Lemma small_step_seq_iter : forall (c0 c1 : Cmd L) (sigma sigma' : State L),
    small_step (c0, sigma) (Skip, sigma') ->
    small_step (Seq c0 c1, sigma) (c1, sigma').
Proof.
    intros * Hss.
    eapply rtc_r; [| by apply os_seq].
    remember (c0, sigma) as cs0; remember (Skip, sigma') as cs0'.
    revert c0 sigma sigma' Heqcs0 Heqcs0'.
    induction Hss; intros; subst.
    - by inversion Heqcs0'; subst.
    - destruct y as (c0'', sigma0''); econstructor.
      + by apply os_seq_struct.
      + by apply IHHss.
Qed.

Lemma small_step_skip : forall (c' : Cmd L) (sigma sigma' : State L),
    small_step (Skip, sigma) (c', sigma') -> c' = Skip /\ sigma = sigma'.
Proof.
    by intros *; inversion 1 as [| ? ? ? Hss]; subst; [| inversion Hss].
Qed.


Lemma n_small_steps_seq_rev  : forall (n : nat) (c0 c1 : Cmd L) (sigma sigma' : State L),
    nsteps one_step n (Seq c0 c1, sigma) (Skip, sigma') ->
    exists (sigma'' : State L) (n0 n1 : nat),
        nsteps one_step n0 (c0, sigma) (Skip, sigma'') /\
        nsteps one_step n1 (c1, sigma'') (Skip, sigma') /\
        n0 + n1 < n.
Proof.
    induction n; intros * Hns; [by inversion Hns |].
    inversion Hns; subst; inversion H0; subst.
    - exists sigma, 0, n; split_and!; [by constructor | done | by lia].
    - apply IHn in H1 as (sigma'' & n0' & n1 & Hc0 & Hc1 & Hlt).
      exists sigma'', (S n0'), n1; split_and!; [by econstructor | done | by lia].
Qed.

Lemma small_step_seq_rev : forall (c0 c1 : Cmd L) (sigma sigma' : State L),
    small_step (Seq c0 c1, sigma) (Skip, sigma') ->
    exists (sigma'' : State L),
        small_step (c0, sigma) (Skip, sigma'') /\
        small_step (c1, sigma'') (Skip, sigma').
Proof.
    intros * Hss.
    apply rtc_nsteps in Hss as [n Hss].
    apply n_small_steps_seq_rev in Hss as (sigma'' & n0 & n1 & Hc0 & Hc1 & _).
    by exists sigma''; split; apply rtc_nsteps; eexists.
Qed.

Lemma small_step_equiv_big_step : forall (c : Cmd L) (sigma sigma' : State L),
    big_step c sigma sigma' <-> small_step (c, sigma) (Skip, sigma').
Proof.
    split.
    - intros [Hbs]; induction Hbs.
      + done.
      + by apply rtc_once; constructor.
      + etransitivity; [| done].
        by apply small_step_seq_iter.
      + eapply rtc_l; [by constructor | done].
      + eapply rtc_l; [by constructor | done].
      + eapply rtc_l; [by constructor |].
        by apply rtc_once; constructor.
      + eapply rtc_l; [by constructor |].
        eapply rtc_l; [by apply os_if_true |].
        etransitivity; [| done].
        by apply small_step_seq_iter.
    - revert sigma sigma'; induction c; intros * Hss.
      + apply small_step_skip in Hss as [_ ->].
        by constructor; constructor.
      + inversion Hss; subst; inversion H; subst.
        apply small_step_skip in H0 as [_ <-].
        by constructor; constructor.
      + apply small_step_seq_rev in Hss as (sigma'' & Hss1 & Hss2).
        destruct (IHc1 _ _ Hss1).
        destruct (IHc2 _ _ Hss2).
        by constructor; econstructor.
      + inversion Hss; subst; inversion H; subst.
        * destruct (IHc1 _ _ H0).
          by constructor; eapply bs_if_true.
        * destruct (IHc2 _ _ H0).
          by constructor; eapply bs_if_false.
      + apply rtc_nsteps in Hss as [n Hss].
        revert sigma sigma' Hss.
        induction n as [n Hind] using (well_founded_ind lt_wf); intros.
        inversion Hss; subst; inversion H; subst.
        inversion H0; subst; inversion H1; subst.
        * apply n_small_steps_seq_rev in H2 as (sigma'' & nc & nw & Hc & Hw & Hlt).
          apply Hind in Hw as [Hw]; [| by lia].
          assert (big_step c sigma sigma'') as [Hbs_c]
            by (apply IHc, rtc_nsteps; eexists; done).
          by constructor; eapply bs_while_true.
        * inversion H2; subst; [| by inversion H3].
          by constructor; apply bs_while_false.
Qed.

End sec_small_step.
