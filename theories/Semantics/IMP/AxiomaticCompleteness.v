From stdpp Require Import prelude finite.
From Coq Require Import Classical FunctionalExtensionality.
From sets Require Import Functions Ensemble.

From Semantics Require Import Syntax State Denotational Axiomatic GoedelBeta.


Section sec_axiomatic_completeness.

Context `{EqDecision L} `{EqDecision V}.

Section sec_goedel.

Context `{Infinite V}.

Definition eb_mod (a b m : EAExp L V) (k := fresh (alog_vars a ∪ alog_vars b ∪ alog_vars m)): EBExp L V :=
  EAnd (EAnd (EALe (EAVal 0)  a) (ENot (EALe b (EAVal 0))))
  (eb_exists k (EAnd (EAnd (EAnd
    (EALe (EAVal 0) (LVar k))
    (EALe (EMul (LVar k) b) a)
    ) (ENot (EALe (EMul (EPlus (LVar k) (EAVal 1)) b) a))
    ) (EAEq m (EMinus a (EMul (LVar k) b))))).

Lemma satsi_mod :
    forall (a b m : EAExp L V) (sigma : State L) (I : State V),
    satsi sigma I (eb_mod a b m)
      <->
    (eaeval sigma I a >= 0)%Z /\ (eaeval sigma I b > 0)%Z /\
    ((eaeval sigma I a) mod (eaeval sigma I b))%Z = eaeval sigma I m.
Proof.
    intros.
    unfold eb_mod.
    rewrite !satsi_and, satsi_exists.
    repeat setoid_rewrite satsi_and.
    setoid_rewrite satsi_not.
    repeat setoid_rewrite satsi_le.
    repeat setoid_rewrite satsi_eq.
    cbn; setoid_rewrite fn_update_eq.
    remember (fresh _) as k.
    assert (k ∉ alog_vars a ∪ alog_vars b ∪ alog_vars m)
      by (subst k; apply is_fresh).
    setoid_rewrite eaeval_update_I; [| by set_solver..].
    clear.
    generalize (eaeval sigma I a) as A; intro A.
    generalize (eaeval sigma I b) as B; intro B.
    generalize (eaeval sigma I m) as M; intro M.
    unfold Z.modulo.
    destruct Z.div_eucl as (d', m') eqn: Hdm.
    pose (Hdiv_mod := Z_div_mod_full A B); rewrite Hdm in Hdiv_mod; clear Hdm.
    split.
    - intros ([Ha Hb] & d & [[Hd0 Hd1] Hd2] & Hdm).
      split; [by lia |].
      split; [by lia |].
      destruct Hdiv_mod as [-> [Hrem | Hrem]]; [by lia | | by lia].
      cut (d = d'); [by lia |]; clear Hdm.
      assert (d - d' < 1)%Z by nia.
      assert (d - d' > -1)%Z by nia.
      by lia.
    - intros (Ha & Hb & <-).
      destruct Hdiv_mod as [-> [Hrem | Hrem]]; [by lia | | by lia].
      split; [by lia |].
      exists d'.
      split; [by nia | by lia].
Qed.

Definition eb_beta (a b i x : EAExp L V) : EBExp L V :=
    EAnd (EAnd (EALe (EAVal 0) b) (EALe (EAVal 0) i))
    (eb_mod a (EPlus (EAVal 1) (EMul (EPlus (EAVal 1) i) b)) x).

Lemma satsi_beta : forall (a b i x : EAExp L V) (sigma : State L) (I : State V),
    satsi sigma I (eb_beta a b i x)
      <->
    (eaeval sigma I a >=0)%Z /\
    (eaeval sigma I b >=0)%Z /\
    (eaeval sigma I i >=0)%Z /\
    eaeval sigma I x
      =
    Z.of_nat (beta_fn (Z.to_nat (eaeval sigma I a)) (Z.to_nat (eaeval sigma I b)) (Z.to_nat (eaeval sigma I i))).
Proof.
    intros.
    unfold eb_beta, beta_fn; rewrite !satsi_and, satsi_mod, !satsi_le; cbn.
    generalize (eaeval sigma I a) as A; intro A.
    generalize (eaeval sigma I b) as B; intro B.
    generalize (eaeval sigma I i) as J; intro J.
    generalize (eaeval sigma I x) as X; intro X.
    destruct PeanoNat.Nat.divmod as (q, r) eqn:Hdm.
    specialize
      (PeanoNat.Nat.divmod_spec
        (Z.to_nat A) (Z.to_nat B + Z.to_nat J * Z.to_nat B)
        0 (Z.to_nat B + Z.to_nat J * Z.to_nat B)).
    rewrite Hdm; clear Hdm.
    intros [Hdm Hr]; [done |].
    unfold Z.modulo.
    destruct Z.div_eucl as (d', m') eqn: Hdm'.
    pose (Hdiv_mod := Z_div_mod_full A (1 + (1 + J) * B)); rewrite Hdm' in Hdiv_mod; clear Hdm'.
    split.
    - intros ([Hb Hj] & Ha & Hd & <-).
      split; [by lia |].
      split; [by lia |].
      split; [by lia |].
      destruct Hdiv_mod as [-> [Hm' | Hm']]; [by lia | | by lia].
      cbn.
      clear a b i x.
      assert
          (Hdm' : ((1 + B + J * B) * (d' - Z.of_nat q))%Z
            =
           (B + J *  B - Z.of_nat r - m')%Z)
          by lia.
      clear Hdm.
      cut (d' = Z.of_nat q); [by lia |].
      assert (Hd' : (1 + B + J * B > 0)%Z) by nia.
      assert (Hrm' : (- (1 + B + J * B) < (B + J *  B - Z.of_nat r - m') < 1 + B + J * B)%Z) by lia.
      clear Hm' Hd.
      assert (Hqd'lt' : ((1 + B + J * B) * (d' - Z.of_nat q - 1) < 0)%Z ) by lia.
      assert (Hqs'gt' : ((1 + B + J * B) * ((d' - Z.of_nat q) + 1) > 0)%Z ) by lia.
      apply Z.lt_mul_0 in Hqd'lt' as [|[_ Hqd'lt'']]; [by lia |].
      apply Zmult_gt_0_reg_l in Hqs'gt'; [| done].
      by lia.
    - intros (Ha & Hb & Hj & ->).
      split_and!; [by lia.. |].
      assert
          (Hdm' : ((1 + B + J * B) * (d' - Z.of_nat q))%Z
            =
           (B + J *  B - Z.of_nat r - m')%Z)
          by lia.
      clear Hdm.
      destruct Hdiv_mod as [-> [Hm' | Hm']]; [by lia | | by lia].
      cbn.
      cut (d' = Z.of_nat q); [by lia |].
      assert (Hd' : (1 + B + J * B > 0)%Z) by nia.
      assert (Hrm' : (- (1 + B + J * B) < (B + J *  B - Z.of_nat r - m') < 1 + B + J * B)%Z) by lia.
      assert (Hqd'lt' : ((1 + B + J * B) * (d' - Z.of_nat q - 1) < 0)%Z ) by lia.
      assert (Hqs'gt' : ((1 + B + J * B) * ((d' - Z.of_nat q) + 1) > 0)%Z ) by lia.
      apply Z.lt_mul_0 in Hqd'lt' as [|[_ Hqd'lt'']]; [by lia |].
      apply Zmult_gt_0_reg_l in Hqs'gt'; [| done].
      by lia.
Qed.

Definition eb_beta_z_helper (x y : EAExp L V) (z := fresh (alog_vars x ∪ alog_vars y)) : EBExp L V :=
    EAnd (EALe (EAVal 0) x)
    (eb_exists z
        (EAnd (EALe (EAVal 0) (LVar z))
         (EAnd (eb_impl (EAEq x (EMul (EAVal 2) (LVar z))) (EAEq y (LVar z)))
               (eb_impl (EAEq x (EPlus (EMul (EAVal 2) (LVar z)) (EAVal 1))) (EAEq y (EMinus (EAVal 0) (LVar z))))))).

Lemma satsi_beta_z_helper: forall (x y : EAExp L V) (sigma : State L) (I : State V),
    satsi sigma I (eb_beta_z_helper x y)
      <->
    (eaeval sigma I x >= 0)%Z
      /\
    beta_z_helper (Z.to_nat (eaeval sigma I x)) (eaeval sigma I y).
Proof.
    intros; unfold eb_beta_z_helper, beta_z_helper.
    rewrite satsi_and, satsi_exists.
    do 2 setoid_rewrite satsi_and.
    setoid_rewrite classical_satsi_impl.
    setoid_rewrite satsi_eq.
    setoid_rewrite satsi_le.
    cbn.
    setoid_rewrite fn_update_eq.
    remember (fresh _) as k.
    assert (Hk: k ∉ alog_vars x ∪ alog_vars y)
      by (subst k; apply is_fresh).
    setoid_rewrite eaeval_update_I; [| by set_solver..].
    clear k Heqk Hk.
    generalize (eaeval sigma I x) as X; intro X.
    generalize (eaeval sigma I y) as Y; intro Y.
    split.
    - intros (HX & z & Hz & Heven & Hodd).
      split; [by lia |].
      by exists (Z.to_nat z); split; lia.
    - intros (HX & z & Heven & Hodd).
      split; [by lia |].
      by exists (Z.of_nat z); lia.
Qed.

Definition eb_beta_z (n m j y : EAExp L V)
    (x := fresh (alog_vars n ∪ alog_vars m ∪ alog_vars j ∪ alog_vars y)) : EBExp L V :=
    eb_exists x
        (EAnd (eb_beta n m j (LVar x)) (eb_beta_z_helper (LVar x) y)).

Lemma satsi_beta_z : forall (n m j y : EAExp L V) (sigma : State L) (I : State V),
    satsi sigma I (eb_beta_z n m j y)
      <->
    (eaeval sigma I n >= 0)%Z
      /\
    (eaeval sigma I m >= 0)%Z
      /\
    (eaeval sigma I j >= 0)%Z
      /\
    beta_z (Z.to_nat (eaeval sigma I n)) (Z.to_nat (eaeval sigma I m)) (Z.to_nat (eaeval sigma I j)) (eaeval sigma I y).
Proof.
    intros; unfold eb_beta_z, beta_z.
    rewrite satsi_exists.
    setoid_rewrite satsi_and.
    setoid_rewrite satsi_beta.
    setoid_rewrite satsi_beta_z_helper.
    setoid_rewrite fn_update_eq.
    remember (fresh _) as k.
    assert (Hk: k ∉ alog_vars n ∪ alog_vars m ∪ alog_vars j ∪ alog_vars y)
      by (subst k; apply is_fresh).
    setoid_rewrite eaeval_update_I; [| by set_solver..].
    clear k Heqk Hk.
    generalize (eaeval sigma I n); intro N.
    generalize (eaeval sigma I m); intro M.
    generalize (eaeval sigma I j); intro J.
    generalize (eaeval sigma I y); intro Y.
    generalize (beta_fn (Z.to_nat N) (Z.to_nat M) (Z.to_nat J)); intro B.
    split.
    - intros (z & (Hn & Hm & Hj & ->) & Hz & Hbeta).
      by rewrite Nat2Z.id in Hbeta.
    - intros (Hn & Hm & Hj & Hbeta).
      exists (Z.of_nat B).
      rewrite Nat2Z.id.
      by split_and!; [..| lia |].
Qed.

End sec_goedel.

Section sec_weakest_precondition.

Definition ws (c : Cmd L) (B : EBExp L V) (I : State V) : Ensemble (State L) :=
    fun (sigma : State L) =>
    forall (sigma' : State L), (sigma, sigma') ∈ denotc c -> satsi sigma' I B.

Lemma ws_weakest :
  forall (A B : EBExp L V) (c : Cmd L) (I : State V),
  ht_sati I (ht A c B)
    <->
  sem I A ⊆ ws c B I.
Proof. done. Qed.

Definition WeakestPrecondition (A : EBExp L V) (c : Cmd L) (B : EBExp L V) : Prop :=
    forall (I : State V), sem I A ≡ ws c B I.

Section sec_wp_oracle.

Context
    (wp : forall  (c : Cmd L) (B : EBExp L V), {A : EBExp L V | WeakestPrecondition A c B}).

Lemma wp_oracle_weakest : forall (A : EBExp L V) (c : Cmd L) (B : EBExp L V),
    ht_sat (ht A c B) -> sat (eb_impl A (` (wp c B))).
Proof.
    intros * Hht sigma I.
    specialize (Hht I).
    rewrite ws_weakest in Hht.
    destruct (wp c B) as [A' HA']; rewrite classical_satsi_impl; intro HA.
    by apply HA', Hht.
Qed.

Lemma wp_oracle_skip : forall (B : EBExp L V),
    sat (eb_iff (` (wp Skip B))  B).
Proof.
    intros; destruct wp as [A Hwp].
    intros sigma I; apply satsi_iff; split.
    - by intro HA; apply Hwp in HA; apply HA.
    - intro HB; apply Hwp.
      by intro sigma'; inversion 1; subst.
Qed.

Lemma wp_oracle_asgn : forall (B : EBExp L V) (l : L) (a : AExp L),
    sat (eb_iff (` (wp (Asgn l a) B)) (bsubst B subst0 (mk_subst [(l, a)]))).
Proof.
    intros; destruct wp as [A Hwp].
    intros sigma I; apply satsi_iff; split.
    - intro HA; apply Hwp in HA.
      by apply satsi_subst_loc, HA; constructor.
    - intro HB; apply Hwp.
      intro sigma'; inversion 1; subst.
      by apply satsi_subst_loc.
Qed.

Lemma wp_oracle_seq : forall (B : EBExp L V) (c1 c2 : Cmd L),
    sat (eb_iff (` (wp (Seq c1 c2) B)) (` (wp c1 (` (wp c2 B))))).
Proof.
    intros.
    destruct (wp (Seq c1 c2) B) as [A Hseq].
    destruct (wp c2 B) as [A2 Hc2]; cbn.
    destruct (wp c1 A2) as [A1 Hc1]; cbn.
    intros sigma I; apply satsi_iff; split.
    - intros HA; apply Hseq in HA.
      apply Hc1.
      intros sigma' Hss'.
      apply Hc2.
      intros sigma'' Hss''.
      by apply HA; econstructor.
    - intros HA1; apply Hseq.
      intros sigma' Hss'.
      apply elem_of_fwd_relation_composition in Hss' as (sigma'' & Hss'' & Hss''').
      eapply Hc2; [| done].
      by eapply Hc1.
Qed.

Lemma wp_oracle_if : forall (B : EBExp L V) (b : BExp L) (c1 c2 : Cmd L),
    sat (eb_iff (` (wp (If b c1 c2) B)) (EOr (EAnd b (` (wp c1 B))) (EAnd (ENot b) (` (wp c2 B))))).
Proof.
    intros.
    destruct (wp (If b c1 c2) B) as [A Hif].
    destruct (wp c1 B) as [A1 Hc1]; cbn.
    destruct (wp c2 B) as [A2 Hc2]; cbn.
    intros sigma I.
    rewrite satsi_iff, satsi_or, !satsi_and, satsi_not; split.
    - intros HA; apply Hif in HA.
      rewrite satsi_eval.
      destruct (decide (denotb b sigma = true)); [left | right]; (split; [done |]).
      + apply Hc1; intros sigma' Hss'; apply HA.
        by apply elem_of_relation_selector; left.
      + apply Hc2; intros sigma' Hss'; apply HA.
        apply elem_of_relation_selector; right; split; [| done].
        by destruct denotb.
    - rewrite satsi_eval. intros [[Hb HA1] | [Hnb HA2]]; apply Hif;
        intros sigma' Hss'; apply elem_of_relation_selector in Hss' as [[]|[]].
      + by eapply Hc1.
      + by congruence.
      + by congruence.
      + by eapply Hc2.
Qed.

Lemma wp_oracle_while_inv : forall (B : EBExp L V) (b : BExp L) (c : Cmd L),
    ht_sat (ht (EAnd (` (wp (While b c) B)) b) c (` (wp (While b c) B))).
Proof.
    intros.
    destruct (wp (While b c) B) as [A Hwhile]; cbn.
    intros I sigma Hpre sigma' Hss'; cbn in *.
    apply Hwhile; intros sigma'' Hss''.
    apply satsi_and in Hpre as [HA Hb].
    apply satsi_eval in Hb.
    apply Hwhile with sigma; [done |].
    apply knaster_tarski_lfp_fix; [by typeclasses eauto |].
    apply elem_of_while_step; right.
    split; [done |].
    by exists sigma'.
Qed.

Lemma wp_oracle_while_exit : forall (B : EBExp L V) (b : BExp L) (c : Cmd L),
    sat (eb_impl (EAnd (` (wp (While b c) B)) (ENot b)) B).
Proof.
    intros.
    destruct (wp (While b c) B) as [A Hwhile]; intros sigma I; cbn.
    rewrite classical_satsi_impl, satsi_and, satsi_not, satsi_eval.
    intros [HA Hb].
    apply Hwhile in HA; apply HA.
    apply knaster_tarski_lfp_fix; [by typeclasses eauto |].
    by right; [destruct denotb | constructor].
Qed.

Lemma wp_oracle_ht_ded :
    forall (c : Cmd L) (B : EBExp L V), ht_ded (ht (` (wp c B)) c B).
Proof.
    induction c; intros B; [eapply ht_cons;
        [| econstructor | by intros sigma I; apply classical_satsi_impl]..|].
    - by apply sat_iff_lr, wp_oracle_skip.
    - by apply sat_iff_lr, wp_oracle_asgn.
    - by apply sat_iff_lr, wp_oracle_seq.
    - by apply IHc1.
    - by apply IHc2.
    - by apply sat_iff_lr, wp_oracle_if.
    - eapply ht_cons; cycle 2; [by intros sigma I; apply classical_satsi_impl | | by apply IHc1].
      intros I sigma.
      rewrite classical_satsi_impl, satsi_and, satsi_or, !satsi_and, satsi_not.
      by tauto.
    - eapply ht_cons; cycle 2; [by intros sigma I; apply classical_satsi_impl | | by apply IHc2].
      intros I sigma.
      rewrite classical_satsi_impl, satsi_and, satsi_or, !satsi_and, satsi_not.
      by tauto.
    - eapply ht_cons; cycle 1;
        [constructor | by apply wp_oracle_while_exit | by intros ? ?; apply classical_satsi_impl].
      eapply ht_cons; cycle 2; [by intros ? ?; apply classical_satsi_impl | | apply IHc].
      by apply wp_oracle_weakest, wp_oracle_while_inv.
Qed.

Lemma wp_oracle_completeness :
    forall (A : EBExp L V) (c : Cmd L) (B : EBExp L V),
    ht_sat (ht A c B) -> ht_ded (ht A c B).
Proof.
    intros * Hht.
    eapply ht_cons; cycle 2;
      [by intros ? ?; apply classical_satsi_impl | | by apply wp_oracle_ht_ded].
    by apply wp_oracle_weakest.
Qed.

End sec_wp_oracle.

Section sec_wp_while.

Context
    (b : BExp L) (c : Cmd L) (w : Cmd L := While b c)
    (B : EBExp L V)
    (relevant_vars : list L := elements (bloc_vars B ∪ cloc_vars (V := V) w))
    .

Inductive WhileOpenSequence : State L -> list (State L) -> State L -> Prop :=
| ws_zero : forall (sigma : State L),
    WhileOpenSequence sigma [sigma] sigma
| ws_more : forall (sigma sigma' sigmaf : State L) (trace : list (State L)),
    denotb b sigma = true ->
    (sigma, sigma') ∈ denotc c ->
    WhileOpenSequence sigma' trace sigmaf ->
    WhileOpenSequence sigma (sigma :: trace) sigmaf
.

Lemma wos_first : forall (sigma sigma' : State L) (trace : list (State L)),
    WhileOpenSequence sigma trace sigma' -> head trace = Some sigma.
Proof. by intros *; inversion 1; subst. Qed.

Lemma wos_last : forall (sigma sigma' : State L) (trace : list (State L)),
    WhileOpenSequence sigma trace sigma' -> last trace = Some sigma'.
Proof.
    intros *; induction 1; [done |].
    by rewrite last_cons, IHWhileOpenSequence.
Qed.

Record WhileSequence (sigma : State L) (trace : list (State L)) (sigma' : State L) : Prop :=
{
  ws_open : WhileOpenSequence sigma trace sigma';
  ws_done : denotb b sigma' = false;
}.

Lemma ws_first : forall (sigma sigma' : State L) (trace : list (State L)),
    WhileSequence sigma trace sigma' -> head trace = Some sigma.
Proof. by intros * []; eapply wos_first. Qed.

Lemma ws_last : forall (sigma sigma' : State L) (trace : list (State L)),
    WhileSequence sigma trace sigma' -> last trace = Some sigma'.
Proof. by intros * []; eapply wos_last. Qed.

Lemma wp_claim1 :
    forall  (sigma sigma' : State L),
    (sigma, sigma') ∈ denotc w
      <->
    exists (trace : list (State L)),
    WhileSequence sigma trace sigma'.
Proof.
    intros; split.
    - intro Hw.
      pose (W (ss' : State L * State L) :=
        exists (trace : list (State L)), WhileSequence ss'.1 trace ss'.2).
      cut (denotc w ⊆ W);
        [by intro Hincl; apply Hincl in Hw; apply Hw |].
      apply knaster_tarski_least_pre_fixpoint.
      clear.
      intros (sigma, sigma').
      unfold while_step; rewrite elem_of_relation_selector, elem_of_fwd_relation_composition.
      intros [(Hb & sigma'' & Hc & trace & ? & ?) | [Hb Hdelta]].
      + by exists (sigma :: trace); constructor; [econstructor |].
      + inversion Hdelta; subst.
        by exists [sigma']; constructor; [constructor |].
    - intros [trace [Hw Hlst]].
      induction Hw; (apply knaster_tarski_lfp_fix; [by typeclasses eauto |]).
      + apply elem_of_relation_selector; right.
        by split; [| constructor].
      + apply elem_of_relation_selector; left.
        split; [done |].
        apply elem_of_fwd_relation_composition.
        specialize (IHHw Hlst).
        by eexists.
Qed.

Lemma wp_claim2 : forall (sigma : State L) (I : State V),
    sigma ∈ ws w B I
      <->
    forall (sigma' : State L) (trace : list (State L)),
        WhileOpenSequence sigma trace sigma' ->
        satsi sigma' I (EOr b B).
Proof.
    intros. apply forall_proper; intros sigma'.
    rewrite wp_claim1.
    split; cycle 1.
    - intros Hall (trace & Hw & Hlst).
      specialize (Hall _ Hw).
      apply satsi_or in Hall as [Hb |]; [| done].
      by apply satsi_eval in Hb; rewrite Hb in Hlst.
    - intros Hex trace Htrace.
      rewrite satsi_or, satsi_eval.
      destruct (denotb b sigma') eqn:Hb; [by left |].
      right; apply Hex.
      by exists trace; split.
Qed.

End sec_wp_while.

Fixpoint wp (c : Cmd L) (B : EBExp L V) :=
match c with
| Skip => B
| Asgn X a => bsubst B subst0 (mk_subst [(X, a)])
| Seq c0 c1 => wp c0 (wp c1 B)
| If b c0 c1 => EOr (EAnd b (wp c0 B)) (EAnd (ENot b) (wp c1 B))
| _ => B
end.

End sec_weakest_precondition.
End sec_axiomatic_completeness.
