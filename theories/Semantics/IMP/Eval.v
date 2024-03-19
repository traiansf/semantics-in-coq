From stdpp Require Import prelude.

From Semantics Require Import Syntax State.

Section sec_eval.

Context `{EqDecision L}.

Definition aeval (sigma : State L) : AExp L -> Z :=
    fix eval (a : AExp L) :=
    match a with
    | AVal n => n
    | Var x => sigma x
    | Plus a1 a2 => (eval a1 + eval a2)%Z
    | Minus a1 a2 => (eval a1 - eval a2)%Z
    | Mul a1 a2 => (eval a1 * eval a2)%Z
    end.


Definition beval (sigma : State L) : BExp L -> bool :=
    fix eval (b : BExp L) :=
    match b with
    | BVal b => b
    | AEq a1 a2 => bool_decide (aeval sigma a1 = aeval sigma a2)
    | ALe a1 a2 => bool_decide (aeval sigma a1 <= aeval sigma a2)%Z
    | Not b => negb (eval b)
    | And b1 b2 => andb (eval b1) (eval b2)
    | Or b1 b2 => orb (eval b1) (eval b2)
    end.

End sec_eval.
