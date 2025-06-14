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

Arguments AVal {L}%_type_scope _%_Z_scope : assert.
Arguments Var {L}%_type_scope _ : assert.
Arguments Plus {L}%_type_scope _ _ : assert.
Arguments Minus {L}%_type_scope _ _ : assert.
Arguments Mul {L}%_type_scope _ _ : assert.

Arguments BVal {L}%_type_scope _%_bool_scope : assert.
Arguments AEq {L}%_type_scope _ _ : assert.
Arguments ALe {L}%_type_scope _ _ : assert.
Arguments Not {L}%_type_scope _ : assert.
Arguments And {L}%_type_scope _ _ : assert.
Arguments Or {L}%_type_scope _ _ : assert.

Arguments Skip {L}%_type_scope : assert.
Arguments Asgn {L}%_type_scope _ _ : assert.
Arguments Seq {L}%_type_scope _ _ : assert.
Arguments If {L}%_type_scope _ _ _ : assert.
Arguments While {L}%_type_scope _ _ : assert.
