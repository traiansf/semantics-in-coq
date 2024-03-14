From stdpp Require Import prelude.

From Semantics Require Import Syntax State.

Definition aeval (sigma : State) : AExp -> Z :=
    fix eval (a : AExp) :=
    match a with
    | AVal n => n
    | Var x => sigma x
    | Plus a1 a2 => (eval a1 + eval a2)%Z
    | Minus a1 a2 => (eval a1 - eval a2)%Z
    | Mul a1 a2 => (eval a1 * eval a2)%Z
    end.


Definition beval (sigma : State) : BExp -> bool :=
    fix eval (b : BExp) :=
    match b with
    | BVal b => b
    | AEq a1 a2 => bool_decide (aeval sigma a1 = aeval sigma a2)
    | ALe a1 a2 => bool_decide (aeval sigma a1 <= aeval sigma a2)%Z
    | Not b => negb (eval b)
    | And b1 b2 => andb (eval b1) (eval b2)
    | Or b1 b2 => orb (eval b1) (eval b2)
    end.
