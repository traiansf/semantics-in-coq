From stdpp Require Import prelude.
From Coq Require Import Classical FunctionalExtensionality.
From sets Require Import Functions Ensemble.

From Semantics.Utils Require Import SetsExtras.
From Semantics.IMP Require Import Syntax State Denotational.

Inductive EAExp (L V : Type) : Type :=
    | LVar : V -> EAExp L V
    | EAVal : Z -> EAExp L V
    | EVar : L -> EAExp L V
    | EPlus : EAExp L V -> EAExp L V -> EAExp L V
    | EMinus : EAExp L V -> EAExp L V -> EAExp L V
    | EMul : EAExp L V -> EAExp L V -> EAExp L V.

Arguments LVar {L V}%type_scope _ : assert.
Arguments EAVal {L V}%type_scope _%Z_scope : assert.
Arguments EVar {L V}%type_scope _%nat_scope : assert.
Arguments EPlus {L V}%type_scope _ _ : assert.
Arguments EMinus {L V}%type_scope _ _ : assert.
Arguments EMul {L V}%type_scope _ _ : assert.

Inductive EBExp (L V : Type) : Type :=
    | EBVal : bool -> EBExp L V
    | EAEq : EAExp L V -> EAExp L V -> EBExp L V
    | EALe : EAExp L V -> EAExp L V -> EBExp L V
    | ENot : EBExp L V -> EBExp L V
    | EAnd : EBExp L V -> EBExp L V -> EBExp L V
    | EOr : EBExp L V -> EBExp L V -> EBExp L V
    | Forall : V -> EBExp L V -> EBExp L V
    .

Arguments EBVal {L V}%type_scope _%bool_scope : assert.
Arguments EAEq {L V}%type_scope _ _ : assert.
Arguments EALe {L V}%type_scope _ _ : assert.
Arguments ENot {L V}%type_scope _ : assert.
Arguments EAnd {L V}%type_scope _ _ : assert.
Arguments EOr {L V}%type_scope _ _ : assert.
Arguments Forall {L V}%type_scope _ _ : assert.

Section sec_axiomatic.

Context `{EqDecision L} `{EqDecision V}.

Fixpoint aexp_to_eaexp (a : AExp L) : EAExp L V :=
  match a with
  | AVal z => EAVal z
  | Var x => EVar x
  | Plus a1 a2 => EPlus (aexp_to_eaexp a1)  (aexp_to_eaexp a2)
  | Minus a1 a2 => EMinus (aexp_to_eaexp a1)  (aexp_to_eaexp a2)
  | Mul a1 a2 => EMul (aexp_to_eaexp a1)  (aexp_to_eaexp a2)
  end.

Fixpoint aloc_vars (a : EAExp L V) : listset L :=
  match a with
  | EAVal z => ∅
  | EVar x => {[x]}
  | LVar x => ∅
  | EPlus a1 a2 => aloc_vars a1 ∪ aloc_vars a2
  | EMinus a1 a2 => aloc_vars a1 ∪ aloc_vars a2
  | EMul a1 a2 => aloc_vars a1 ∪ aloc_vars a2
  end.

Fixpoint alog_vars (a : EAExp L V) : listset V :=
  match a with
  | EAVal z => ∅
  | EVar x => ∅
  | LVar x => {[x]}
  | EPlus a1 a2 => alog_vars a1 ∪ alog_vars a2
  | EMinus a1 a2 => alog_vars a1 ∪ alog_vars a2
  | EMul a1 a2 => alog_vars a1 ∪ alog_vars a2
  end.

Global Coercion aexp_to_eaexp : AExp >-> EAExp.

Definition eb_impl (b1 b2: EBExp L V) : EBExp L V :=
  EOr (ENot b1) b2.

Definition eb_iff  (b1 b2: EBExp L V) : EBExp L V :=
  EAnd (eb_impl b1 b2) (eb_impl b2 b1).

Definition eb_exists (x : V) (b : EBExp L V) : EBExp L V :=
    ENot (Forall x (ENot b)).

Fixpoint bexp_to_ebexp (b : BExp L) : EBExp L V :=
  match b with
  | BVal t => EBVal t
  | AEq a1 a2 => EAEq  (aexp_to_eaexp a1)  (aexp_to_eaexp a2)
  | ALe a1 a2 => EALe  (aexp_to_eaexp a1)  (aexp_to_eaexp a2)
  | Not b => ENot (bexp_to_ebexp b)
  | And b1 b2 => EAnd (bexp_to_ebexp b1) (bexp_to_ebexp b2)
  | Or b1 b2 => EOr (bexp_to_ebexp b1) (bexp_to_ebexp b2)
  end.

Fixpoint bloc_vars (b : EBExp L V) : listset L :=
  match b with
  | EBVal t => ∅
  | EAEq a1 a2 => aloc_vars a1 ∪ aloc_vars a2
  | EALe a1 a2 => aloc_vars a1 ∪ aloc_vars a2
  | ENot b => bloc_vars b
  | EAnd b1 b2 => bloc_vars b1 ∪ bloc_vars b2
  | EOr b1 b2 => bloc_vars b1 ∪ bloc_vars b2
  | Forall x b => bloc_vars b
  end.

Fixpoint blog_vars (b : EBExp L V) : listset V :=
  match b with
  | EBVal t => ∅
  | EAEq a1 a2 => alog_vars a1 ∪ alog_vars a2
  | EALe a1 a2 => alog_vars a1 ∪ alog_vars a2
  | ENot b => blog_vars b
  | EAnd b1 b2 => blog_vars b1 ∪ blog_vars b2
  | EOr b1 b2 => blog_vars b1 ∪ blog_vars b2
  | Forall x b => blog_vars b ∖ {[x]}
  end.

Global Coercion bexp_to_ebexp : BExp >-> EBExp.

Fixpoint cloc_vars (c : Cmd L) : listset L :=
match c with
| Skip => ∅
| Asgn x a => aloc_vars a ∪ {[x]}
| Seq c0 c1 => cloc_vars c0 ∪ cloc_vars c1
| If b c0 c1 => bloc_vars b ∪ cloc_vars c0 ∪ cloc_vars c1
| While b c => bloc_vars b ∪ cloc_vars c
end.

Definition substitution (T : Type) : Type := T -> option (AExp L).

Definition asubst (a : EAExp L V) (logv : substitution V) (locv : substitution L) : EAExp L V :=
  (fix go (a : EAExp L V) : EAExp L V :=
  match a with
  | LVar x => default (LVar x) (aexp_to_eaexp <$> logv x)
  | EAVal z => EAVal z
  | EVar x => default (EVar x) (aexp_to_eaexp <$> locv x)
  | EPlus a1 a2 => EPlus (go a1)  (go a2)
  | EMinus a1 a2 => EMinus (go a1) (go a2)
  | EMul a1 a2 => EMul (go a1)  (go a2)
  end) a.

Fixpoint bsubst  (b : EBExp L V) (logv : substitution V) (locv : substitution L) : EBExp L V :=
  match b with
  | EBVal t => EBVal t
  | EAEq a1 a2 => EAEq (asubst a1 logv locv) (asubst a2 logv locv)
  | EALe a1 a2 => EALe (asubst a1 logv locv) (asubst a2 logv locv)
  | ENot b => ENot (bsubst b logv locv)
  | EAnd b1 b2 => EAnd (bsubst b1 logv locv) (bsubst b2 logv locv)
  | EOr b1 b2 => EOr (bsubst b1 logv locv) (bsubst b2 logv locv)
  | Forall x b => Forall x (bsubst b (fn_update logv x None) locv)
  end.

Definition subst0 {T : Type} : substitution T := const None.

Definition update `{EqDecision T} (subst : substitution T) (sub : list (T * AExp L)) : substitution T :=
  foldr (fun p s => fn_update s p.1 (Some p.2)) subst sub.

Definition mk_subst `{EqDecision T} := @update T _ subst0.

Definition subst_vars `(s : substitution T) : Ensemble T :=
    fun (x : T) => is_Some (s x).

Lemma subst_vars0 {T} : subst_vars (@subst0 T) ≡ ∅.
Proof. by apply equiv_empty; intros x [a Hx]. Qed.

Lemma subst_vars_fn_update_Some `{EqDecision T}:
    forall (s : substitution T) (x : T) (a : AExp L),
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

Lemma subst_vars_update `{EqDecision T} :
    forall (s : substitution T) (sub : list (T * AExp L)),
    subst_vars (update s sub) ≡ subst_vars s ∪ list_to_set (map fst sub).
Proof.
    intros *; revert s; induction sub; [by set_solver |].
    intro s; cbn.
    unfold update in IHsub; rewrite subst_vars_fn_update_Some, IHsub.
    by set_solver.
Qed.

Lemma subst_vars_mk_subst `{EqDecision T}: forall (sub : list (T * AExp L)),
    subst_vars (mk_subst sub) ≡ list_to_set (map fst sub).
Proof.
    intros; unfold mk_subst.
    rewrite subst_vars_update, subst_vars0.
    by set_solver.
Qed.

Lemma asubst_id :
    forall (a : EAExp L V) (slog : substitution V) (sloc : substitution L),
    list_to_set (elements (aloc_vars a)) ∩ subst_vars sloc ≡ ∅ ->
    list_to_set (elements (alog_vars a)) ∩ subst_vars slog ≡ ∅ ->
    asubst a slog sloc = a.
Proof.
    intros *; induction a; intros Hloc Hlog.
    - cbn; cut (slog v = None); [by intros -> |].
      cbn in Hlog.
      assert (Hn : v ∉ subst_vars slog) by set_solver.
      destruct (slog v) eqn:Hslog; [| done].
      by contradict Hn; eexists.
    - done.
    - cbn; cut (sloc l = None); [by intros -> |].
      cbn in Hloc.
      assert (Hn : l ∉ subst_vars sloc) by set_solver.
      destruct (sloc l) eqn:Hslog; [| done].
      by contradict Hn; eexists.
    - cbn; setoid_rewrite IHa1; [| by set_solver..].
      by setoid_rewrite IHa2; [| set_solver..].
    - cbn; setoid_rewrite IHa1; [| by set_solver..].
      by setoid_rewrite IHa2; [| set_solver..].
    - cbn; setoid_rewrite IHa1; [| by set_solver..].
      by setoid_rewrite IHa2; [| set_solver..].
Qed.

Lemma bsubst_id : forall (b : EBExp L V) (slog : substitution V) (sloc : substitution L),
    list_to_set (elements (bloc_vars b)) ∩ subst_vars sloc ≡ ∅ ->
    list_to_set (elements (blog_vars b)) ∩ subst_vars slog ≡ ∅ ->
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
      rewrite elem_of_intersection, elem_of_list_to_set, elem_of_elements, elem_of_difference, elem_of_singleton.
      split_and!; [| done | eexists; done].
      by apply elem_of_list_to_set, elem_of_elements in Hx.
Qed.

Definition eaeval (sigma : State L) (I : State V): EAExp L V -> Z :=
    fix eval (a : EAExp L V) :=
    match a with
    | LVar x => I x
    | EAVal n => n
    | EVar x => sigma x
    | EPlus a1 a2 => (eval a1 + eval a2)%Z
    | EMinus a1 a2 => (eval a1 - eval a2)%Z
    | EMul a1 a2 => (eval a1 * eval a2)%Z
    end.

Lemma eaeval_aexp: forall (a : AExp L) (sigma : State L) (I : State V),
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

Lemma eaeval_update_I :
    forall (a : EAExp L V) (sigma : State L) (I : State V) (x : V) (z : Z),
    x ∉ alog_vars a ->
    eaeval sigma (fn_update I x z) a = eaeval sigma I a.
Proof.
    intros *. induction a; cbn; intro Hx.
    - by unfold fn_update; rewrite decide_False by set_solver.
    - done.
    - done.
    - by rewrite IHa1, IHa2 by set_solver.
    - by rewrite IHa1, IHa2 by set_solver.
    - by rewrite IHa1, IHa2 by set_solver.
Qed.

Fixpoint satsi_set (sigma : State L) (I : State V) (b : EBExp L V) : Ensemble True :=
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

Definition satsi (sigma : State L) (I : State V) (b : EBExp L V) : Prop :=
    satsi_set sigma I b ≡ top True.

Lemma satsi_true : forall (sigma : State L) (I : State V), satsi sigma I (BVal true).
Proof. done. Qed.

Lemma satsi_false : forall (sigma : State L) (I : State V), ~ satsi sigma I (BVal false).
Proof.
    intros sigma Interp; unfold satsi; cbn.
    by intro contra; apply top_not_bottom.
Qed.

Lemma satsi_eq : forall (sigma : State L) (I : State V) (a1 a2 : EAExp L V),
    satsi sigma I (EAEq a1 a2) <-> eaeval sigma I a1 = eaeval sigma I a2.
Proof.
    unfold satsi; cbn; split; intros; case_decide.
    - done.
    - by exfalso; apply top_not_bottom.
    - done.
    - done.
Qed.

Lemma satsi_le : forall (sigma : State L) (I : State V) (a1 a2 : EAExp L V),
    satsi sigma I (EALe a1 a2) <-> (eaeval sigma I a1 <= eaeval sigma I a2)%Z.
Proof.
    unfold satsi; cbn; split; intros; case_decide.
    - done.
    - by exfalso; apply top_not_bottom.
    - done.
    - done.
Qed.

Lemma satsi_not : forall (sigma : State L) (I : State V) (b : EBExp L V),
    satsi sigma I (ENot b) <-> ~ satsi sigma I b.
Proof.
    intros; unfold satsi; cbn.
    by rewrite !top_char, elem_of_complement.
Qed.

Lemma satsi_and_intro : forall (sigma : State L) (I : State V) (b1 b2 : EBExp L V),
     satsi sigma I b1 -> satsi sigma I b2 -> satsi sigma I (EAnd b1 b2).
Proof. by set_solver. Qed.

Lemma satsi_and_elim_l : forall (sigma : State L) (I : State V) (b1 b2 : EBExp L V),
    satsi sigma I (EAnd b1 b2) -> satsi sigma I b1.
Proof. by set_solver. Qed.

Lemma satsi_and_elim_r : forall (sigma : State L) (I : State V) (b1 b2 : EBExp L V),
    satsi sigma I (EAnd b1 b2) -> satsi sigma I b2.
Proof. by set_solver. Qed.

Lemma satsi_and : forall (sigma : State L) (I : State V) (b1 b2 : EBExp L V),
    satsi sigma I (EAnd b1 b2) <-> satsi sigma I b1 /\ satsi sigma I b2.
Proof. by set_solver. Qed.

Lemma satsi_or : forall (sigma : State L) (I : State V) (b1 b2 : EBExp L V),
    satsi sigma I (EOr b1 b2) <-> satsi sigma I b1 \/ satsi sigma I b2.
Proof. by intros; unfold satsi; cbn; rewrite !top_char, elem_of_union. Qed.

Lemma satsi_forall : forall (sigma : State L) (I : State V) (x : V) (b : EBExp L V),
    satsi sigma I (Forall x b) <-> forall (z : Z), satsi sigma (fn_update I x z) b.
Proof.
    intros; unfold satsi; cbn.
    setoid_rewrite top_char.
    by rewrite elem_of_indexed_intersection.
Qed.

Lemma satsi_exists : forall (sigma : State L) (I : State V) (x : V) (b : EBExp L V),
    satsi sigma I (eb_exists x b) <-> exists (z : Z), satsi sigma (fn_update I x z) b.
Proof.
    intros; unfold eb_exists; rewrite satsi_not, satsi_forall.
    setoid_rewrite satsi_not.
    split.
    - by intro; apply not_all_not_ex.
    - intros [z Hz] Hall.
      by eapply Hall.
Qed.

Lemma satsi_mp :  forall (sigma : State L) (I : State V) (b1 b2 : EBExp L V),
    satsi sigma I (eb_impl b1 b2) -> satsi sigma I b1 -> satsi sigma I b2.
Proof.
    intros *; unfold eb_impl.
    rewrite satsi_or, satsi_not.
    by intros [].
Qed.

Lemma classical_satsi_impl :  forall (sigma : State L) (I : State V) (b1 b2 : EBExp L V),
    satsi sigma I (eb_impl b1 b2) <-> (satsi sigma I b1 -> satsi sigma I b2).
Proof.
    split; [by apply satsi_mp |].
    intros *; unfold eb_impl.
    rewrite satsi_or, satsi_not.
    intros Himpl.
    destruct (classic (satsi sigma I b1)).
    - by right; apply Himpl.
    - by left.
Qed.

Lemma satsi_iff : forall (sigma : State L) (I : State V) (b1 b2 : EBExp L V),
    satsi sigma I (eb_iff b1 b2) <-> (satsi sigma I b1 <-> satsi sigma I b2).
Proof.
    intros; unfold eb_iff.
    rewrite satsi_and, !classical_satsi_impl.
    by tauto.
Qed.

Lemma satsi_iff_lr : forall (sigma : State L) (I : State V) (b1 b2 : EBExp L V),
    satsi sigma I (eb_iff b1 b2) -> (satsi sigma I (eb_impl b1 b2)).
Proof. by intros *; rewrite satsi_iff, classical_satsi_impl; tauto. Qed.

Lemma satsi_iff_rl : forall (sigma : State L) (I : State V) (b1 b2 : EBExp L V),
    satsi sigma I (eb_iff b1 b2) -> (satsi sigma I (eb_impl b2 b1)).
Proof. by intros *; rewrite satsi_iff, classical_satsi_impl; tauto. Qed.

Lemma satsi_eval : forall (sigma : State L) (I : State V) (b : BExp L),
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

Definition sati (b : EBExp L V) : Prop :=
    forall (sigma : State L) (I : State V), satsi sigma I b.

Definition sat (b : EBExp L V) : Prop :=
    forall (sigma : State L) (I : State V), satsi sigma I b.


Lemma sat_true : sat (BVal true).
Proof. done. Qed.

Lemma sat_and_intro : forall (b1 b2 : EBExp L V),
     sat b1 -> sat b2 -> sat (EAnd b1 b2).
Proof.
    by intros * Hb1 Hb2 sigma I; apply satsi_and_intro; [apply Hb1 | apply Hb2].
Qed.

Lemma sat_and_elim_l : forall (b1 b2 : EBExp L V),
    sat (EAnd b1 b2) -> sat b1.
Proof. by intros * Hand sigma I; eapply satsi_and_elim_l, Hand. Qed.

Lemma sat_and_elim_r : forall (b1 b2 : EBExp L V),
    sat (EAnd b1 b2) -> sat b2.
Proof. by intros * Hand sigma I; eapply satsi_and_elim_r, Hand. Qed.

Lemma sat_and : forall (b1 b2 : EBExp L V),
    sat (EAnd b1 b2) <-> sat b1 /\ sat b2.
Proof.
    split.
    - by split; [eapply sat_and_elim_l | eapply sat_and_elim_r].
    - by intros []; apply sat_and_intro.
Qed.

Lemma sat_or_intro_l : forall (b1 b2 : EBExp L V),
    sat b1 -> sat (EOr b1 b2).
Proof. by intros * Hb1 sigma I; apply satsi_or; left; apply Hb1. Qed.

Lemma sat_or_intro_r : forall (b1 b2 : EBExp L V),
    sat b2 -> sat (EOr b1 b2).
Proof. by intros * Hb2 sigma I; apply satsi_or; right; apply Hb2. Qed.

Lemma sat_mp :  forall (b1 b2 : EBExp L V),
    sat (eb_impl b1 b2) -> sat b1 -> sat b2.
Proof.
    by intros * Hb12 Hb1 sigma I; eapply satsi_mp; [apply Hb12 | apply Hb1].
Qed.

Lemma sat_iff : forall (b1 b2 : EBExp L V),
    sat (eb_iff b1 b2) -> (sat b1 <-> sat b2).
Proof.
    intros * Hiff; split.
    - intros Hb1 sigma I.
      by specialize (Hiff sigma I); rewrite satsi_iff in Hiff; apply Hiff, Hb1.
    - intros Hb2 sigma I.
      by specialize (Hiff sigma I); rewrite satsi_iff in Hiff; apply Hiff, Hb2.
Qed.

Lemma sat_iff_lr : forall (b1 b2 : EBExp L V),
    sat (eb_iff b1 b2) -> sat (eb_impl b1 b2).
Proof.
    intros * Hiff sigma I.
    by specialize (Hiff sigma I); apply satsi_iff_lr in Hiff; apply Hiff.
Qed.

Lemma sat_iff_rl : forall (b1 b2 : EBExp L V),
    sat (eb_iff b1 b2) -> sat (eb_impl b2 b1).
Proof.
    intros * Hiff sigma I.
    by specialize (Hiff sigma I); apply satsi_iff_rl in Hiff; apply Hiff.
Qed.

Definition sem (I : State V) (A : EBExp L V) : Ensemble (State L) :=
    fun (sigma : State L) => satsi sigma I A.

Record HoareTriple : Type := ht
{
    pre_condition : EBExp L V;
    command : Cmd L;
    post_condition : EBExp L V;
}.

Definition ht_satsi (sigma : State L) (I : State V) (t : HoareTriple) : Prop :=
    satsi sigma I (pre_condition t) ->
    forall (sigma' : State L), (sigma, sigma') ∈ denotc (command t) ->
    satsi sigma' I (post_condition t).

Definition ht_sati (I : State V) (t : HoareTriple) : Prop :=
    forall (sigma : State L), ht_satsi sigma I t.

Lemma ht_sati_alt: forall (I : State V) (t : HoareTriple),
    ht_sati I t
      <->
    forall (sigma sigma' : State L), (sigma, sigma') ∈ denotc (command t) ->
    satsi sigma I (pre_condition t) ->
    satsi sigma' I (post_condition t).
Proof.
    split; [by intros Ht **; eapply Ht |].
    by intros Hall ? ? **; eapply Hall.
Qed.

Definition ht_sat (t : HoareTriple) : Prop :=
    forall (I : State V), ht_sati I t.

Inductive ht_ded : HoareTriple -> Prop :=
| ht_skip : forall (B : EBExp L V), ht_ded (ht B Skip B)
| ht_asgn : forall (B : EBExp L V) (x : L) (a : AExp L),
    ht_ded (ht (bsubst B subst0 (mk_subst [(x, a)])) (Asgn x a) B)
| ht_seq : forall (A B C : EBExp L V) (c0 c1 : Cmd L),
    ht_ded (ht A c0 B) -> ht_ded (ht B c1 C) -> ht_ded (ht A (Seq c0 c1) C)
| ht_if : forall (A B : EBExp L V) (b : BExp L) (c0 c1 : Cmd L),
    ht_ded (ht (EAnd A b) c0 B) -> ht_ded (ht (EAnd A (ENot b)) c1 B) ->
    ht_ded (ht A (If b c0 c1) B)
| ht_while : forall (A : EBExp L V) (b : BExp L) (c : Cmd L),
    ht_ded (ht (EAnd A b) c A) ->
    ht_ded (ht A (While b c) (EAnd A (ENot b)))
| ht_cons : forall (A A' B B' : EBExp L V) (c : Cmd L),
    sat (eb_impl A A') -> ht_ded (ht A' c B') -> sat (eb_impl B' B) ->
    ht_ded (ht A c B)
.

Lemma ht_asgn_derived: forall (X : L) (a : AExp L) (A : EBExp L V),
    X ∉ aloc_vars a ∪ bloc_vars A ->
    ht_ded (ht A (Asgn X a) (EAnd A (EAEq (EVar X) a))).
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
  (n s i : L)
  (Hns : n <> s)
  (Hsi : s <> i)
  (Hin : i <> n)
  .

Definition w : Cmd L :=
    While (ALe (Var i) (Var n))
      (Seq
      (Asgn s (Plus (Var s) (Var i)))
      (Asgn i (Plus (Var i) (AVal 1)))).

Definition p : Cmd L :=
  Seq (Seq
  (Asgn s (AVal 0))
  (Asgn i (AVal 0)))
  w.

Definition pre : BExp L := ALe (AVal 0) (Var n).
Definition post : BExp L :=
    AEq (Mul (AVal 2) (Var s)) (Mul (Var n) (Plus (Var n) (AVal 1))).

Lemma step_1 : ht_ded (ht
    pre
    (Asgn s (AVal 0))
    (EAnd pre (EAEq (Var s) (AVal 0)))
    ).
Proof. by apply ht_asgn_derived; set_solver. Qed.

Lemma step_2 : ht_ded (ht
    (EAnd pre (EAEq (Var s) (AVal 0)))
    (Asgn i (AVal 0))
    (EAnd (EAnd pre (EAEq (Var s) (AVal 0))) (EAEq (Var i) (AVal 0)))
    ).
Proof. by apply ht_asgn_derived; set_solver. Qed.

Lemma step_12 : ht_ded (ht
    pre
    (Seq (Asgn s (AVal 0)) (Asgn i (AVal 0)))
    (EAnd (EAnd pre (EAEq (Var s) (AVal 0))) (EAEq (Var i) (AVal 0)))
    ).
Proof.
    eapply ht_seq; [apply step_1 | apply step_2].
Qed.

Definition invariant : BExp L := And
    (AEq (Mul (AVal 2) (Var s)) (Mul (Var i) (Minus (Var i) (AVal 1))))
    (ALe (Var i) (Plus (Var n) (AVal 1))).

Lemma loop_inv_1 : ht_ded (ht
    (bsubst invariant subst0 (mk_subst [(i, Plus (Var i) (AVal 1))]))
    (Asgn i (Plus (Var i) (AVal 1)))
    invariant
    ).
Proof. by apply ht_asgn. Qed.

Lemma loop_inv_2 : ht_ded (ht
    (bsubst
      (bsubst invariant subst0 (mk_subst [(i, Plus (Var i) (AVal 1))]))
      subst0 (mk_subst [(s, Plus (Var s) (Var i))]))
    (Asgn s (Plus (Var s) (Var i)))
    (bsubst invariant subst0 (mk_subst [(i, Plus (Var i) (AVal 1))]))
    ).
Proof. by apply ht_asgn. Qed.

Lemma loop_inv_12 : ht_ded (ht
    (bsubst
      (bsubst invariant subst0 (mk_subst [(i, Plus (Var i) (AVal 1))]))
      subst0 (mk_subst [(s, Plus (Var s) (Var i))]))
    (Seq
      (Asgn s (Plus (Var s) (Var i)))
      (Asgn i (Plus (Var i) (AVal 1))))
    invariant).
Proof.
    eapply ht_seq; [apply loop_inv_2 | apply loop_inv_1].
Qed.

Lemma loop_inv : ht_ded (ht
    (EAnd invariant (ALe (Var i) (Var n)))
    (Seq
      (Asgn s (Plus (Var s) (Var i)))
      (Asgn i (Plus (Var i) (AVal 1))))
    invariant
    ).
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

Lemma p_while : ht_ded (ht
    (EAnd (EAnd pre (EAEq (Var s) (AVal 0))) (EAEq (Var i) (AVal 0)))
    w
    post).
Proof.
    eapply ht_cons; [| apply ht_while, loop_inv |];
      intros sigma I; apply classical_satsi_impl.
    - unfold invariant; cbn; rewrite !satsi_and, !satsi_eq, !satsi_le; cbn.
      by lia.
    - unfold invariant; cbn; rewrite !satsi_and, satsi_not, !satsi_eq, !satsi_le; cbn.
      by nia.
Qed.

Lemma p_correct : ht_ded (ht pre p post).
Proof.
    by eapply ht_seq; [apply step_12 | apply p_while].
Qed.

End sec_Hoare_logic_example.

Lemma eaeval_subst_loc :
  forall  (sigma : State L) (I : State V) (e : EAExp L V) (x : L) (a : AExp L),
  eaeval sigma I (asubst e subst0 (mk_subst [(x, a)]))
    =
  eaeval (State.update sigma x (denota a sigma)) I e.
Proof.
  induction e; intros.
  - done.
  - done.
  - cbn. unfold State.update, fn_update.
    case_decide; cbn; [| done].
    by apply eaeval_aexp.
  - by cbn; rewrite <- IHe1, <- IHe2.
  - by cbn; rewrite <- IHe1, <- IHe2.
  - by cbn; rewrite <- IHe1, <- IHe2.
Qed.

Lemma satsi_subst_loc :
  forall (sigma : State L) (I : State V) (e : EBExp L V) (x : L) (a : AExp L),
  satsi sigma I (bsubst e subst0 (mk_subst [(x, a)]))
    <->
  satsi (State.update sigma x (denota a sigma)) I e.
Proof.
  intros sigma I e; revert I; induction e; intros.
  - done.
  - by cbn; rewrite !satsi_eq, <- !eaeval_subst_loc.
  - by cbn; rewrite !satsi_le, <- !eaeval_subst_loc.
  - by cbn; rewrite !satsi_not, <- IHe.
  - by cbn; rewrite !satsi_and, <- IHe1, <- IHe2.
  - by cbn; rewrite !satsi_or, <- IHe1, <- IHe2.
  - cbn; rewrite !satsi_forall.
    apply forall_proper; intro z.
    rewrite <- IHe.
    cut (fn_update subst0 v None = subst0); [by intros ->|].
    extensionality y.
    by unfold fn_update; case_decide.
Qed.

Theorem ht_soundness : forall (A B : EBExp L V) (c : Cmd L),
    ht_ded (ht A c B) -> ht_sat (ht A c B).
Proof.
    intros * Hht I. apply ht_sati_alt.
    remember {| command := c|} as ht; revert A B c Heqht.
    induction Hht; cbn in *; intros * ? sigma sigma' Hdenot Hpre; inversion Heqht; subst.
    - by inversion Hdenot; subst.
    - inversion Hdenot; subst.
      by apply satsi_subst_loc.
    - inversion Hdenot; subst.
      eapply IHHht2; [done.. |]; cbn.
      by eapply IHHht1.
    - inversion Hdenot; subst.
      + eapply IHHht1; [done.. |].
        apply satsi_and.
        split; [done |].
        by apply satsi_eval.
      + eapply IHHht2; [done.. |].
        rewrite satsi_and, satsi_not, satsi_eval.
        split; [done |].
        by rewrite H1.
    - pose (W (ss' : State L * State L) := satsi ss'.1 I A0 -> satsi ss'.2 I (EAnd A0 (ENot b))).
      cut (lfp (while_step (denotb b) (denotc c)) ⊆ W);
        [by intros Hincl; apply Hincl in Hdenot; apply Hdenot |].
      apply knaster_tarski_least_pre_fixpoint.
      clear -IHHht.
      intros (sigma, sigma').
      unfold while_step.
      rewrite elem_of_relation_selector, elem_of_fwd_relation_composition.
      intros [(Hb & sigma'' & Hc & Hw)|[Hb Hdelta]] Hsigma.
      + eapply Hw, IHHht; [done.. |].
        apply satsi_and; split; [done |].
        by apply satsi_eval.
      + inversion Hdelta; subst; cbn in *.
        rewrite satsi_and, satsi_not; split; [done |].
        by rewrite satsi_eval, Hb.
    - eapply classical_satsi_impl; [by apply H0 |].
      eapply IHHht; [done.. |].
      by eapply classical_satsi_impl; [apply H |].
Qed.

End sec_axiomatic.
