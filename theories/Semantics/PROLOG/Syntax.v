From Semantics.FOL Require Import Syntax.

Record definite_clause (sigma : signature) (V : Type) : Type := mk_definite_clause
{
cl_head : RelAtom sigma V;
cl_body : RelAtomConjunction sigma V;
}.

Arguments cl_head {sigma V%type_scope} d : assert.
Arguments cl_body {sigma V%type_scope} d : assert.


Definition definite_clause_to_rel_formula
    `(cl : definite_clause sign V) : RelFormula sign V :=
    Impl (ra_conjunction_to_rel_formula (cl_body cl)) (Atomic (cl_head cl)).

Coercion definite_clause_to_rel_formula :
    definite_clause >-> RelFormula.

Record definite_goal (sigma : signature) (V : Type) : Type := mk_definite_goal
{
  get_definite_goal : RelAtomConjunction sigma V;
}.

Arguments get_definite_goal {sigma V%type_scope} d : assert.
Arguments mk_definite_goal {sigma V%type_scope} get_definite_goal : assert.

Definition definite_goal_to_rel_formula
    `(cl : definite_goal sigma V) : RelFormula sigma V :=
    ra_conjunction_to_rel_formula (get_definite_goal cl).

Coercion definite_goal_to_rel_formula :
    definite_goal >-> RelFormula.

Definition program (sigma : signature) (V : Type) : Type := list (definite_clause sigma V).

Definition query (sigma : signature) (V : Type) : Type := definite_goal sigma V.
