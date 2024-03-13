From stdpp Require Import prelude.

Inductive AExp : Type :=
    | AVal : Z -> AExp
    | var : nat -> AExp
    | Plus : AExp -> AExp -> AExp
    | Minus : AExp -> AExp -> AExp
    | Mul : AExp -> AExp -> AExp.

Inductive BExp : Type :=
    | BVal : bool -> BExp
    | AEq : AExp -> AExp -> BExp
    | ALe : AExp -> AExp -> BExp
    | Not : BExp -> BExp
    | And : BExp -> BExp -> BExp
    | Or : BExp -> BExp -> BExp.

Inductive Cmd : Type :=
    | Skip : Cmd
    | Asgn : nat -> AExp -> Cmd
    | Seq : Cmd -> Cmd -> Cmd
    | If : BExp -> Cmd -> Cmd -> Cmd
    | While : BExp -> Cmd -> Cmd.
