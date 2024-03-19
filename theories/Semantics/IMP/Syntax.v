From stdpp Require Import prelude.

Section sec_syntax.

Context (L : Type).

Inductive AExp : Type :=
    | AVal : Z -> AExp
    | Var : L -> AExp
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
    | Asgn : L -> AExp -> Cmd
    | Seq : Cmd -> Cmd -> Cmd
    | If : BExp -> Cmd -> Cmd -> Cmd
    | While : BExp -> Cmd -> Cmd.

End sec_syntax.

Arguments AVal {L}%type_scope _%Z_scope : assert.
Arguments Var {L}%type_scope _ : assert.
Arguments Plus {L}%type_scope _ _ : assert.
Arguments Minus {L}%type_scope _ _ : assert.
Arguments Mul {L}%type_scope _ _ : assert.

Arguments BVal {L}%type_scope _%bool_scope : assert.
Arguments AEq {L}%type_scope _ _ : assert.
Arguments ALe {L}%type_scope _ _ : assert.
Arguments Not {L}%type_scope _ : assert.
Arguments And {L}%type_scope _ _ : assert.
Arguments Or {L}%type_scope _ _ : assert.

Arguments Skip {L}%type_scope : assert.
Arguments Asgn {L}%type_scope _ _ : assert.
Arguments Seq {L}%type_scope _ _ : assert.
Arguments If {L}%type_scope _ _ _ : assert.
Arguments While {L}%type_scope _ _ : assert.
