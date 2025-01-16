From stdpp Require Import prelude.

Definition cBool : Type := forall A, A -> A -> A.
Definition ctrue : cBool := fun A t f => t.
Definition cfalse : cBool := fun A t f => f.
Definition cbool : forall A, A -> A -> cBool -> A := fun A vt vf b => b A vt vf.

Lemma cbool_true : forall A vt vf, cbool A vt vf ctrue = vt.
Proof. done. Qed.

Lemma cbool_false : forall A vt vf, cbool A vt vf cfalse = vf.
Proof. done. Qed.

Definition bif {A : Type} (b : cBool) (bthen belse : A) : A :=
    cbool A bthen belse b.

Definition bnot (b : cBool) : cBool := fun A => bif b (cfalse  A) (ctrue  A).
Definition band (b1 b2 : cBool) : cBool := fun A => bif b1 (b2 A) (cfalse A).
Definition bor (b1 b2 : cBool) : cBool := fun A => bif b1 (ctrue A) (b2 A).

Lemma bnot_truth_table :
    bnot ctrue = cfalse ∧ bnot cfalse = ctrue.
Proof. done. Qed.

Lemma band_truth_table :
    band ctrue ctrue = ctrue ∧
    band ctrue cfalse = cfalse ∧
    band cfalse ctrue = cfalse ∧
    band cfalse cfalse = cfalse.
Proof. done. Qed.

Lemma bor_truth_table :
    bor ctrue  ctrue  = ctrue ∧
    bor ctrue  cfalse = ctrue ∧
    bor cfalse ctrue  = ctrue ∧
    bor cfalse cfalse = cfalse.
Proof. done. Qed.


Class MaybeClass {MayBe : Type -> Type} 
    (mc_nothing : forall (A : Type), MayBe A)
    (mc_just : forall (A : Type) (a : A), MayBe A)
    (mc_rec : forall (A B : Type), B -> (A -> B) -> MayBe A -> B) := {
    mc_rec_nothing : forall A B (vnothing : B) (fjust : A -> B), mc_rec A B vnothing fjust (mc_nothing A) = vnothing;
    mc_rec_just : forall A B (vnothing : B) (fjust : A -> B) (x : A), mc_rec A B vnothing fjust (mc_just A x) = (fjust x);
}.

Section sec_maybe_fns.

Context
    `{MaybeClass}.

Definition from_maybe {A} (a : A) (ma : MayBe A) : A :=
    mc_rec A A a id ma.

Definition isNothing `(ma : MayBe A) : cBool :=
    mc_rec A cBool ctrue (const cfalse) ma.

Definition isJust `(ma : MayBe A) : cBool :=
    bnot (isNothing ma) .
    

