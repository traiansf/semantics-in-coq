From stdpp Require Import prelude.
From sets Require Import Functions Ensemble.

From Semantics Require Import Syntax State Eval.

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

Fixpoint bsubst  (b : EBExp) (logv : substitution) (locv : substitution) : EBExp :=
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
    eaeval sigma I a = aeval sigma a.
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
