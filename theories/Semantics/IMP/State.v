From stdpp Require Import prelude.
From sets Require Import Functions.

Definition State : Type := nat -> Z.

Definition update: State -> nat -> Z -> State := fn_update.
