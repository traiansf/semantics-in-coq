From stdpp Require Import prelude.
From Coq Require Import Classical.
From sets Require Import Functions Ensemble.

From Semantics Require Import Syntax State Denotational.

Inductive EAExp : Type :=
    | LVar : nat -> EAExp
    | EAVal : Z -> EAExp
    | EVar : nat -> EAExp
    | EPlus : EAExp -> EAExp -> EAExp
    | EMinus : EAExp -> EAExp -> EAExp
    | EMul : EAExp -> EAExp -> EAExp.

Fixpoint aexp_to_eaexp (a : AExp) : EAExp :=
  match a with
  | AVal z => EAVal z
  | Var x => EVar x
  | Plus a1 a2 => EPlus (aexp_to_eaexp a1)  (aexp_to_eaexp a2)
  | Minus a1 a2 => EMinus (aexp_to_eaexp a1)  (aexp_to_eaexp a2)
  | Mul a1 a2 => EMul (aexp_to_eaexp a1)  (aexp_to_eaexp a2)
  end.

Fixpoint aloc_vars (a : EAExp) : Ensemble nat :=
  match a with
  | EAVal z => ∅
  | EVar x => {[x]}
  | LVar x => ∅
  | EPlus a1 a2 => aloc_vars a1 ∪ aloc_vars a2
  | EMinus a1 a2 => aloc_vars a1 ∪ aloc_vars a2
  | EMul a1 a2 => aloc_vars a1 ∪ aloc_vars a2
  end.

Fixpoint alog_vars (a : EAExp) : Ensemble nat :=
  match a with
  | EAVal z => ∅
  | EVar x => ∅
  | LVar x => {[x]}
  | EPlus a1 a2 => alog_vars a1 ∪ alog_vars a2
  | EMinus a1 a2 => alog_vars a1 ∪ alog_vars a2
  | EMul a1 a2 => alog_vars a1 ∪ alog_vars a2
  end.

Coercion aexp_to_eaexp : AExp >-> EAExp.

Inductive EBExp : Type :=
    | EBVal : bool -> EBExp
    | EAEq : EAExp -> EAExp -> EBExp
    | EALe : EAExp -> EAExp -> EBExp
    | ENot : EBExp -> EBExp
    | EAnd : EBExp -> EBExp -> EBExp
    | EOr : EBExp -> EBExp -> EBExp
    | Forall : nat -> EBExp -> EBExp
    .

Definition eimpl (b1 b2: EBExp) : EBExp :=
  EOr (ENot b1) b2.

Fixpoint bexp_to_ebexp (b : BExp) : EBExp :=
  match b with
  | BVal t => EBVal t
  | AEq a1 a2 => EAEq  (aexp_to_eaexp a1)  (aexp_to_eaexp a2)
  | ALe a1 a2 => EALe  (aexp_to_eaexp a1)  (aexp_to_eaexp a2)
  | Not b => ENot (bexp_to_ebexp b)
  | And b1 b2 => EAnd (bexp_to_ebexp b1) (bexp_to_ebexp b2)
  | Or b1 b2 => EOr (bexp_to_ebexp b1) (bexp_to_ebexp b2)
  end.

Fixpoint bloc_vars (b : EBExp) : Ensemble nat :=
  match b with
  | EBVal t => ∅
  | EAEq a1 a2 => aloc_vars a1 ∪ aloc_vars a2
  | EALe a1 a2 => aloc_vars a1 ∪ aloc_vars a2
  | ENot b => bloc_vars b
  | EAnd b1 b2 => bloc_vars b1 ∪ bloc_vars b2
  | EOr b1 b2 => bloc_vars b1 ∪ bloc_vars b2
  | Forall x b => bloc_vars b
  end.

Fixpoint blog_vars (b : EBExp) : Ensemble nat :=
  match b with
  | EBVal t => ∅
  | EAEq a1 a2 => alog_vars a1 ∪ alog_vars a2
  | EALe a1 a2 => alog_vars a1 ∪ alog_vars a2
  | ENot b => blog_vars b
  | EAnd b1 b2 => blog_vars b1 ∪ blog_vars b2
  | EOr b1 b2 => blog_vars b1 ∪ blog_vars b2
  | Forall x b => blog_vars b ∖ {[x]}
  end.

Coercion bexp_to_ebexp : BExp >-> EBExp.

Definition substitution : Type := nat -> option AExp.

Definition asubst (a : EAExp) (logv : substitution) (locv : substitution) : EAExp :=
  (fix go (a : EAExp) :EAExp :=
  match a with
  | LVar x => default (LVar x) (aexp_to_eaexp <$> logv x)
  | EAVal z => EAVal z
  | EVar x => default (EVar x) (aexp_to_eaexp <$> locv x)
  | EPlus a1 a2 => EPlus (go a1)  (go a2)
  | EMinus a1 a2 => EMinus (go a1) (go a2)
  | EMul a1 a2 => EMul (go a1)  (go a2)
  end) a.

Fixpoint bsubst  (b : EBExp) (logv locv : substitution) : EBExp :=
  match b with
  | EBVal t => EBVal t
  | EAEq a1 a2 => EAEq (asubst a1 logv locv) (asubst a2 logv locv)
  | EALe a1 a2 => EALe (asubst a1 logv locv) (asubst a2 logv locv)
  | ENot b => ENot (bsubst b logv locv)
  | EAnd b1 b2 => EAnd (bsubst b1 logv locv) (bsubst b2 logv locv)
  | EOr b1 b2 => EOr (bsubst b1 logv locv) (bsubst b2 logv locv)
  | Forall x b => Forall x (bsubst b (fn_update logv x None) locv)
  end.

Definition subst0 : substitution := const None.

Definition update (subst : substitution) (sub : list (nat * AExp)) : substitution :=
  foldr (fun p s => fn_update s p.1 (Some p.2)) subst sub.

Definition mk_subst := update subst0.

Definition subst_vars (s : substitution) : Ensemble nat :=
    fun (x : nat) => is_Some (s x).

Lemma subst_vars0 : subst_vars subst0 ≡ ∅.
Proof. by apply equiv_empty; intros x [a Hx]. Qed.

Lemma subst_vars_fn_update_Some : forall (s : substitution) (x : nat) (a : AExp),
    subst_vars (fn_update s x (Some a)) ≡ subst_vars s ∪ {[x]}.
Proof.
    intros; intro y; rewrite elem_of_union, elem_of_singleton.
    split.
    - intros [b Hy].
      unfold fn_update in Hy.
      by case_decide; [right | left; eexists].
    - intros [[b Hy]| ->].
      + unfold fn_update, subst_vars, elem_of, pow_set_elem_of; cbn.
        by case_decide; eexists.
      + by exists a; rewrite fn_update_eq.
Qed.

Lemma subst_vars_update : forall (s : substitution) (sub : list (nat * AExp)),
    subst_vars (update s sub) ≡ subst_vars s ∪ list_to_set (map fst sub).
Proof.
    intros *; revert s; induction sub; [by set_solver |].
    intro s; cbn.
    rewrite subst_vars_fn_update_Some, IHsub.
    by set_solver.
Qed.

Lemma subst_vars_mk_subst : forall (sub : list (nat * AExp)),
    subst_vars (mk_subst sub) ≡ list_to_set (map fst sub).
Proof.
    intros; unfold mk_subst.
    rewrite subst_vars_update, subst_vars0.
    by set_solver.
Qed.

Lemma asubst_id : forall (a : EAExp) (slog sloc : substitution),
    aloc_vars a ∩ subst_vars sloc ≡ ∅ ->
    alog_vars a ∩ subst_vars slog ≡ ∅ ->
    asubst a slog sloc = a.
Proof.
    intros *; induction a; intros Hloc Hlog.
    - cbn; cut (slog n = None); [by intros -> |].
      cbn in Hlog.
      assert (Hn : n ∉ subst_vars slog) by set_solver.
      destruct (slog n) eqn:Hslog; [| done].
      by contradict Hn; eexists.
    - done.
    - cbn; cut (sloc n = None); [by intros -> |].
      cbn in Hloc.
      assert (Hn : n ∉ subst_vars sloc) by set_solver.
      destruct (sloc n) eqn:Hslog; [| done].
      by contradict Hn; eexists.
    - cbn; setoid_rewrite IHa1; [| by set_solver..].
      by setoid_rewrite IHa2; [| set_solver..].
    - cbn; setoid_rewrite IHa1; [| by set_solver..].
      by setoid_rewrite IHa2; [| set_solver..].
    - cbn; setoid_rewrite IHa1; [| by set_solver..].
      by setoid_rewrite IHa2; [| set_solver..].
Qed.

Lemma bsubst_id : forall (b : EBExp) (slog sloc : substitution),
    bloc_vars b ∩ subst_vars sloc ≡ ∅ ->
    blog_vars b ∩ subst_vars slog ≡ ∅ ->
    bsubst b slog sloc = b.
Proof.
    induction b; intros slog sloc Hloc Hlog.
    - done.
    - by cbn; rewrite !asubst_id by set_solver.
    - by cbn; rewrite !asubst_id by set_solver.
    - by cbn; setoid_rewrite IHb; [| set_solver..].
    - cbn; setoid_rewrite IHb1; [| by set_solver..].
      by setoid_rewrite IHb2; [| set_solver..].
    - cbn; setoid_rewrite IHb1; [| by set_solver..].
      by setoid_rewrite IHb2; [| set_solver..].
    - cbn. rewrite IHb; [done | by set_solver |].
      cbn in Hlog; apply equiv_empty.
      intro x; rewrite elem_of_intersection; intros [Hx [a Ha]].
      unfold fn_update in Ha; case_decide; [done |].
      apply Hlog.
      rewrite elem_of_intersection, elem_of_difference, elem_of_singleton.
      by split_and!; [..| eexists].
Qed.

Definition eaeval (sigma : State) (I : nat -> Z): EAExp -> Z :=
    fix eval (a : EAExp) :=
    match a with
    | LVar x => I x
    | EAVal n => n
    | EVar x => sigma x
    | EPlus a1 a2 => (eval a1 + eval a2)%Z
    | EMinus a1 a2 => (eval a1 - eval a2)%Z
    | EMul a1 a2 => (eval a1 * eval a2)%Z
    end.

Lemma eaeval_aexp: forall (a : AExp) (sigma : State) (I : nat -> Z),
    eaeval sigma I a = denota a sigma.
Proof.
    intros.
    induction a.
    - done.
    - done.
    - by cbn; rewrite IHa1, IHa2.
    - by cbn; rewrite IHa1, IHa2.
    - by cbn; rewrite IHa1, IHa2.
Qed.

Lemma top_char X : X ≡ top True <-> I ∈ X.
Proof.
    rewrite elem_of_equiv_top.
    split; [done |].
    by intros HI [].
Qed.

Lemma bot_char (X : Ensemble True) : X ≡ ∅ <-> I ∉ X.
Proof.
    split; [by set_solver |].
    intros HI.
    apply equiv_empty.
    by intros [] Hx.
Qed.

Lemma top_not_bottom : top True ≢ ∅.
Proof.
    rewrite bot_char.
    by intro contra; apply contra.
Qed.

Fixpoint satsi_set (sigma I : State) (b : EBExp) : Ensemble True :=
match b with
| EBVal true => top True
| EBVal false => ∅
| EAEq a1 a2 => if decide (eaeval sigma I a1 = eaeval sigma I a2) then top True else ∅
| EALe a1 a2 => if decide (eaeval sigma I a1 <= eaeval sigma I a2)%Z then top True else ∅
| ENot b => complement (satsi_set sigma I b)
| EAnd b1 b2 => (satsi_set sigma I b1) ∩ (satsi_set sigma I b2)
| EOr b1 b2 => (satsi_set sigma I b1) ∪ (satsi_set sigma I b2)
| Forall x b => indexed_intersection (fun z : Z => satsi_set sigma (fn_update I x z) b)
end.

Definition satsi (sigma I : State) (b : EBExp) : Prop :=
    satsi_set sigma I b ≡ top True.

Lemma satsi_true : forall (sigma I : State), satsi sigma I (BVal true).
Proof. done. Qed.

Lemma satsi_false : forall (sigma I : State), ~ satsi sigma I (BVal false).
Proof.
    intros sigma Interp; unfold satsi; cbn.
    by intro contra; apply top_not_bottom.
Qed.

Lemma satsi_eq : forall (sigma I : State) (a1 a2 : EAExp),
    satsi sigma I (EAEq a1 a2) <-> eaeval sigma I a1 = eaeval sigma I a2.
Proof.
    unfold satsi; cbn; split; intros; case_decide.
    - done.
    - by exfalso; apply top_not_bottom.
    - done.
    - done.
Qed.

Lemma satsi_le : forall (sigma I : State) (a1 a2 : EAExp),
    satsi sigma I (EALe a1 a2) <-> (eaeval sigma I a1 <= eaeval sigma I a2)%Z.
Proof.
    unfold satsi; cbn; split; intros; case_decide.
    - done.
    - by exfalso; apply top_not_bottom.
    - done.
    - done.
Qed.

Lemma satsi_not : forall (sigma I : State) (b : EBExp),
    satsi sigma I (ENot b) <-> ~ satsi sigma I b.
Proof.
    intros; unfold satsi; cbn.
    by rewrite !top_char, elem_of_complement.
Qed.

Lemma satsi_and_intro : forall (sigma I : State) (b1 b2 : EBExp),
     satsi sigma I b1 -> satsi sigma I b2 -> satsi sigma I (EAnd b1 b2).
Proof. by set_solver. Qed.

Lemma satsi_and_elim_l : forall (sigma I : State) (b1 b2 : EBExp),
    satsi sigma I (EAnd b1 b2) -> satsi sigma I b1. 
Proof. by set_solver. Qed.

Lemma satsi_and_elim_r : forall (sigma I : State) (b1 b2 : EBExp),
    satsi sigma I (EAnd b1 b2) -> satsi sigma I b2. 
Proof. by set_solver. Qed.

Lemma satsi_and : forall (sigma I : State) (b1 b2 : EBExp),
    satsi sigma I (EAnd b1 b2) <-> satsi sigma I b1 /\ satsi sigma I b2.
Proof. by set_solver. Qed.

Lemma satsi_or : forall (sigma I : State) (b1 b2 : EBExp),
    satsi sigma I (EOr b1 b2) <-> satsi sigma I b1 \/ satsi sigma I b2.
Proof. by intros; unfold satsi; cbn; rewrite !top_char, elem_of_union. Qed.

Lemma satsi_forall : forall (sigma I : State) (x : nat) (b : EBExp),
    satsi sigma I (Forall x b) <-> forall (z : Z), satsi sigma (fn_update I x z) b.
Proof.
    intros; unfold satsi; cbn.
    setoid_rewrite top_char.
    by rewrite elem_of_indexed_intersection.
Qed.

Lemma satsi_mp :  forall (sigma I : State) (b1 b2 : EBExp),
    satsi sigma I (eimpl b1 b2) -> satsi sigma I b1 -> satsi sigma I b2.
Proof.
    intros *; unfold eimpl.
    rewrite satsi_or, satsi_not.
    by intros [].
Qed.

Lemma classical_satsi_impl :  forall (sigma I : State) (b1 b2 : EBExp),
    satsi sigma I (eimpl b1 b2) <-> (satsi sigma I b1 -> satsi sigma I b2).
Proof.
    split; [by apply satsi_mp |].
    intros *; unfold eimpl.
    rewrite satsi_or, satsi_not.
    intros Himpl.
    destruct (classic (satsi sigma I b1)).
    - by right; apply Himpl.
    - by left.
Qed.

Lemma satsi_eval : forall (sigma I : State) (b : BExp),
    satsi sigma I b <-> denotb b sigma = true.
Proof.
    intros; induction b.
    - destruct b; [done |]; cbn.
      split; [| done].
      by intro Ha; exfalso; apply top_not_bottom.
    - setoid_rewrite satsi_eq.
      rewrite !eaeval_aexp; cbn; unfold denota.
      by rewrite bool_decide_eq_true.
    - setoid_rewrite satsi_le.
      rewrite !eaeval_aexp; cbn; unfold denota.
      by rewrite bool_decide_eq_true.
    - setoid_rewrite satsi_not.
      setoid_rewrite IHb; cbn.
      rewrite negb_true_iff.
      by unfold denotb; destruct Eval.beval.
    - setoid_rewrite satsi_and.
      setoid_rewrite IHb1; setoid_rewrite IHb2; cbn.
      by rewrite andb_true_iff.
    - setoid_rewrite satsi_or.
      setoid_rewrite IHb1; setoid_rewrite IHb2; cbn.
      by rewrite orb_true_iff.
Qed.

Definition sat (b : EBExp) : Prop :=
    forall (sigma I : State), satsi sigma I b.

Definition sem (I : State) (A : EBExp) : Ensemble State :=
    fun (sigma : State) => satsi sigma I A.

Record HoareTriple : Type := ht
{
    pre_condition : EBExp;
    command : Cmd;
    post_condition : EBExp;
}.

Definition ht_satsi (sigma I : State) (t : HoareTriple) : Prop :=
    satsi sigma I (pre_condition t) ->
    forall (sigma' : State), (sigma, sigma') ∈ denotc (command t) ->
    satsi sigma' I (post_condition t).

Definition ht_sati (I : State) (t : HoareTriple) : Prop :=
    forall (sigma : State), ht_satsi sigma I t.

Lemma ht_sati_alt: forall (I : State) (t : HoareTriple),
    ht_sati I t
      <->
    forall (sigma sigma' : State), (sigma, sigma') ∈ denotc (command t) ->
    satsi sigma I (pre_condition t) ->
    satsi sigma' I (post_condition t).
Proof.
    split; [by intros Ht **; eapply Ht |].
    by intros Hall ? ? **; eapply Hall.
Qed.

Definition ht_sat (t : HoareTriple) : Prop :=
    forall (I : State), ht_sati I t.

Inductive ht_ded : EBExp -> Cmd -> EBExp -> Prop :=
| ht_skip : forall (B : EBExp), ht_ded B Skip B
| ht_asgn : forall (B : EBExp) (x : nat) (a : AExp),
    ht_ded (bsubst B subst0 (mk_subst [(x, a)])) (Asgn x a) B
| ht_seq : forall (A B C : EBExp) (c0 c1 : Cmd),
    ht_ded A c0 B -> ht_ded B c1 C -> ht_ded A (Seq c0 c1) C
| ht_if : forall (A B : EBExp) (b : BExp) (c0 c1 : Cmd),
    ht_ded (EAnd A b) c0 B -> ht_ded (EAnd A (ENot b)) c1 B ->
    ht_ded A (If b c0 c1) B
| ht_while : forall (A : EBExp) (b : BExp) (c : Cmd),
    ht_ded (EAnd A b) c A ->
    ht_ded A (While b c) (EAnd A (ENot b))
| ht_cons : forall (A A' B B' : EBExp) (c : Cmd),
    sat (eimpl A A') -> ht_ded A' c B' -> sat (eimpl B' B) ->
    ht_ded A c B
. 

Lemma ht_asgn_derived: forall (X : nat) (a : AExp) (A : EBExp),
    X ∉ aloc_vars a ∪ bloc_vars A ->
    ht_ded A (Asgn X a) (EAnd A (EAEq (EVar X) a)).
Proof.
    intros * HX.
    eapply ht_cons with (B' :=  (EAnd A (EAEq (EVar X) a)));
        [| apply ht_asgn |]; cbn.
    - rewrite fn_update_eq; cbn.
      intros sigma I.
      apply classical_satsi_impl.
      intro HA.
      rewrite satsi_and, satsi_eq.
      rewrite bsubst_id, asubst_id; [done |..].
      + rewrite subst_vars_fn_update_Some, subst_vars0.
        apply equiv_empty; intros Y.
        rewrite elem_of_intersection, elem_of_union, elem_of_singleton.
        by intros [HYA [| ->]]; set_solver.
      + by rewrite subst_vars0; set_solver.
      + rewrite subst_vars_fn_update_Some, subst_vars0.
        apply equiv_empty; intros Y.
        rewrite elem_of_intersection, elem_of_union, elem_of_singleton.
        by intros [HYA [| ->]]; set_solver.
      + by rewrite subst_vars0; set_solver.
    - by intros sigma I; apply classical_satsi_impl.
Qed.

Section sec_Hoare_logic_example.

Context
  (n s i : nat)
  (Hns : n <> s)
  (Hsi : s <> i)
  (Hin : i <> n)
  .

Definition w : Cmd := 
    While (ALe (Var i) (Var n))
      (Seq
      (Asgn s (Plus (Var s) (Var i)))
      (Asgn i (Plus (Var i) (AVal 1)))).

Definition p : Cmd :=
  Seq (Seq
  (Asgn s (AVal 0))
  (Asgn i (AVal 0)))
  w.

Definition pre : BExp := ALe (AVal 0) (Var n).
Definition post : BExp :=
    AEq (Mul (AVal 2) (Var s)) (Mul (Var n) (Plus (Var n) (AVal 1))).

Lemma step_1 : ht_ded
    pre
    (Asgn s (AVal 0))
    (EAnd pre (EAEq (Var s) (AVal 0))).
Proof. by apply ht_asgn_derived; set_solver. Qed.

Lemma step_2 : ht_ded
    (EAnd pre (EAEq (Var s) (AVal 0)))
    (Asgn i (AVal 0))
    (EAnd (EAnd pre (EAEq (Var s) (AVal 0))) (EAEq (Var i) (AVal 0))).
Proof. by apply ht_asgn_derived; set_solver. Qed.

Lemma step_12 : ht_ded
    pre
    (Seq (Asgn s (AVal 0)) (Asgn i (AVal 0)))
    (EAnd (EAnd pre (EAEq (Var s) (AVal 0))) (EAEq (Var i) (AVal 0))).
Proof.
    eapply ht_seq; [apply step_1 | apply step_2].
Qed.

Definition invariant : BExp := And
    (AEq (Mul (AVal 2) (Var s)) (Mul (Var i) (Minus (Var i) (AVal 1))))
    (ALe (Var i) (Plus (Var n) (AVal 1))).

Lemma loop_inv_1 : ht_ded
    (bsubst invariant subst0 (mk_subst [(i, Plus (Var i) (AVal 1))]))
    (Asgn i (Plus (Var i) (AVal 1)))
    invariant.
Proof. by apply ht_asgn. Qed.

Lemma loop_inv_2 : ht_ded
    (bsubst
      (bsubst invariant subst0 (mk_subst [(i, Plus (Var i) (AVal 1))]))
      subst0 (mk_subst [(s, Plus (Var s) (Var i))]))
    (Asgn s (Plus (Var s) (Var i)))
    (bsubst invariant subst0 (mk_subst [(i, Plus (Var i) (AVal 1))])).
Proof. by apply ht_asgn. Qed.

Lemma loop_inv_12 : ht_ded
    (bsubst
      (bsubst invariant subst0 (mk_subst [(i, Plus (Var i) (AVal 1))]))
      subst0 (mk_subst [(s, Plus (Var s) (Var i))]))
    (Seq
      (Asgn s (Plus (Var s) (Var i)))
      (Asgn i (Plus (Var i) (AVal 1))))
    invariant.
Proof.
    eapply ht_seq; [apply loop_inv_2 | apply loop_inv_1].
Qed.

Lemma loop_inv : ht_ded
    (EAnd invariant (ALe (Var i) (Var n)))
    (Seq
      (Asgn s (Plus (Var s) (Var i)))
      (Asgn i (Plus (Var i) (AVal 1))))
    invariant.
Proof.
    eapply ht_cons with (B' := invariant);
      [| apply loop_inv_12 | by intros sigma I; apply classical_satsi_impl].
    intros sigma I.
    apply classical_satsi_impl.
    unfold invariant; cbn.
    rewrite !satsi_and, !satsi_eq, !satsi_le, !fn_update_eq.
    unfold fn_update.
    rewrite !decide_False by done; cbn.
    rewrite decide_True by done.
    rewrite !decide_False by done; cbn.
    by nia.
Qed.

Lemma p_while : ht_ded
    (EAnd (EAnd pre (EAEq (Var s) (AVal 0))) (EAEq (Var i) (AVal 0)))
    w
    post.
Proof.
    eapply ht_cons; [| apply ht_while, loop_inv |];
      intros sigma I; apply classical_satsi_impl.
    - unfold invariant; cbn; rewrite !satsi_and, !satsi_eq, !satsi_le; cbn.
      by lia.
    - unfold invariant; cbn; rewrite !satsi_and, satsi_not, !satsi_eq, !satsi_le; cbn.
      by nia.
Qed.

Lemma p_correct : ht_ded pre p post.
Proof.
    by eapply ht_seq; [apply step_12 | apply p_while].
Qed.

End sec_Hoare_logic_example.
    