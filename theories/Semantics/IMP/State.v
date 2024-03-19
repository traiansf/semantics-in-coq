From stdpp Require Import prelude.
From sets Require Import Functions.

Definition State (L : Type) : Type := L -> Z.

Definition update `{EqDecision L} : State L -> L -> Z -> State L := fn_update.
