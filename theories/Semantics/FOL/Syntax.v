From stdpp Require Import prelude.

From sets Require Import Ensemble Functions.


Inductive Formula (V : Type) (A : Type -> Type) :=
| Atomic (a : A V)
| Bot
| Impl (phi psi : Formula V A)
| All (x : V) (phi : Formula V A).

Arguments Atomic {V%type_scope A%function_scope} a : assert.
Arguments Bot {V%type_scope A%function_scope} : assert.
Arguments Impl {V%type_scope A%function_scope} phi psi : assert.
Arguments All {V%type_scope A%function_scope} x phi : assert.

Definition f_top {V A} : Formula V A := Impl Bot Bot.
Definition f_neg `(f : Formula V A) := Impl f Bot.
Definition f_and {V A} (f g : Formula V A) := f_neg (Impl f (f_neg g)).
Definition f_or {V A} (f g : Formula V A) := Impl (f_neg f) g.
Definition f_iff {V A} (f g : Formula V A) := f_and (Impl f g) (Impl g f).
Definition f_ex {V A} (x : V) (f : Formula V A) := f_neg (All x (f_neg f)).

Class FreeVars (A V : Type) :=
    free_vars : A -> listset V.
#[global] Hint Mode FreeVars ! - : typeclass_instances.

Fixpoint f_free_vars `{EqDecision V} {A} (a_free_vars : A V -> listset V) (f : Formula V A) : listset V :=
match f with
| Atomic a => a_free_vars a
| Bot => ∅
| Impl f g => f_free_vars a_free_vars f ∪ f_free_vars a_free_vars g
| All x f =>  f_free_vars a_free_vars f ∖ {[x]}
end.

#[export] Instance formula_free_vars `{EqDecision V} `{FreeVars (A V) V} :
    FreeVars (Formula V A) V := f_free_vars free_vars.

Definition statement A `{FreeVars A V} : Ensemble A :=
    fun phi => free_vars phi ≡ ∅.

Record signature : Type := {
symbol : Type;
relation : Type;
s_arity : symbol -> nat;
r_arity : relation -> nat;
}.

Arguments s_arity {s} _: assert.
Arguments r_arity {s} _: assert.

Class EnsuringInhabitation (sigma : signature) :=
    ensures_inhabitation : {s : symbol sigma & s_arity s = 0}.

Section sec_terms.

Context
    (sigma : signature).

Section sec_vterms.

Context
    (V : Type).

Inductive VTerm : Type :=
| Var (v : V)
| App (s : symbol sigma) (t : vec VTerm (s_arity s)).

Definition vterm_rect
  (P : VTerm -> Type) (Plist : forall n, vec VTerm n -> Type)
  (Hvar : forall v : V, P (Var v))
  (Happ : forall (s : symbol sigma),
    forall l : vec VTerm (s_arity s), Plist _ l -> P (App s l))
  (Hnil : Plist 0 [#])
  (Hcons : forall (e : VTerm) (n : nat), P e -> forall l : vec VTerm n, Plist n l -> Plist (S n) (e ::: l)) :
  forall (v : VTerm), P v
  :=
  fix F (e : VTerm) : P e :=
    match e as e0 return (P e0) with
    | Var v => Hvar v
    | App s l' =>
      Happ s l'
        (Vector.t_rect VTerm Plist Hnil (fun e'' n l'' => Hcons e'' n (F e'') l'') (s_arity s) l')
    end.

Definition vterm_rec
  (P : VTerm -> Set) (Plist : forall n, vec VTerm n -> Set) := vterm_rect P Plist.

Lemma vterm_ind
  (P : VTerm -> Prop)
  (Hvar : forall v : V, P (Var v))
  (Happ : forall (s : symbol sigma),
    forall l : vec VTerm (s_arity s), Forall P (vec_to_list l) -> P (App s l)) :
  forall (v : VTerm), P v.
Proof.
    apply vterm_rec with (Plist := fun n l => Forall P (vec_to_list l));
      [done | done |..].
    - by constructor.
    - intros * He l Hl.
      apply Forall_vlookup; intro i; cbn.
      inv_fin i; cbn; [done |].
      by apply Forall_vlookup.
Qed.

End sec_vterms.

Arguments Var {V%type_scope} v : assert.
Arguments App {V%type_scope} s t : assert.

Definition vterm_vars {V} : VTerm V -> listset V :=
    vterm_rect V (fun _ => listset V) (fun n _ => vec (listset V) n)
      (fun v => {[v]})
      (fun _ _ ls => ⋃ ls)
      [#]
      (fun _ _ vt _ vts =>  vt ::: vts).

#[export] Instance vterm_free_vars V : FreeVars (VTerm V) V := vterm_vars.

Lemma vterm_fv_var `(x : V) : free_vars (Var x) = {[x]}.
Proof. done. Qed.

Lemma vterm_fv_app {V} (s : symbol sigma) (ts : vec (VTerm V) (s_arity s)) :
    free_vars (App s ts) = ⋃ vmap free_vars  ts.
Proof. done. Qed.

Definition Term : Type := VTerm False.

Definition term_to_vterm (V : Type) : Term -> VTerm V :=
    vterm_rect False (fun _ => VTerm V) (fun n _ => vec (VTerm V) n)
      (fun x => match x with end)
      (fun sigma _ va => App sigma va)
      [#]
      (fun _ n v0 _ vl => v0 ::: vl).

Lemma term_vars : forall (t : Term), free_vars t ≡ ∅.
Proof.
    induction t using vterm_ind; cbn; [by inversion v |].
    apply empty_union_list, Forall_forall; intros.
    by rewrite elem_of_equiv_empty; intro.
Qed.

Inductive RelAtom (V : Type) :=
| RApp (pi : relation sigma) (t : vec (VTerm V) (r_arity pi)).

Definition rel_atom_vars {V} (ra : RelAtom V) : listset V :=
    match ra with
    | RApp _ pi ts => ⋃ map free_vars (vec_to_list ts)
    end.

#[export] Instance rel_atom_free_vars V : FreeVars (RelAtom V) V := rel_atom_vars.

Inductive EqAtom (V : Type) :=
| REq (l r : VTerm V).

Definition eq_atom_vars {V} (ea : EqAtom V) : listset V :=
    match ea with
    | REq _ l r => free_vars l ∪ free_vars r
    end.

#[export] Instance eq_atom_free_vars V : FreeVars (EqAtom V) V := eq_atom_vars.

Inductive RelEqAtom (V : Type) :=
| ARel (ar : RelAtom V)
| AEq (ae : EqAtom V).

Definition rel_eq_atom_vars {V} (a : RelEqAtom V) : listset V :=
    match a with
    | ARel _ ar => free_vars ar
    | AEq _ ae => free_vars ae
    end.

#[export] Instance rel_eq_atom_free_vars V : FreeVars (RelEqAtom V) V := rel_eq_atom_vars.

Coercion ARel : RelAtom >-> RelEqAtom.
Coercion AEq : EqAtom >-> RelEqAtom.

Definition EqFormula (V : Type) := Formula V EqAtom.

Definition RelFormula (V : Type) := Formula V RelAtom.

Definition RelEqFormula (V : Type) := Formula V RelEqAtom.

Fixpoint formula_eq_to_rel `(f : EqFormula V) : RelEqFormula V :=
match f with
| Atomic eq => Atomic (AEq _ eq)
| Bot => Bot
| Impl f g => Impl (formula_eq_to_rel f) (formula_eq_to_rel g)
| All x f => All x (formula_eq_to_rel f)
end.

Coercion formula_eq_to_rel : EqFormula >-> RelEqFormula.

End sec_terms.

Arguments Var {sigma V%type_scope} v : assert.
Arguments App {sigma V%type_scope} s t : assert.

Arguments RApp {sigma V%type_scope} pi t : assert.
Arguments REq {sigma V%type_scope} l r : assert.

Arguments ARel {sigma V%type_scope} ar : assert.
Arguments AEq {sigma V%type_scope} ae : assert.
