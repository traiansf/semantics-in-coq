From stdpp Require Import prelude.

From sets Require Import Ensemble.

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
