From stdpp Require Import prelude.

Definition State : Type := nat -> Z.

Definition update (sigma : State) (x : nat) (n : Z) (y : nat) : Z :=
    if decide (y = x) then n else sigma y.