From stdpp Require Import prelude.
From Coq Require Import Classical.

From sets Require Import Ensemble Functions.

From Semantics.Utils Require Import SetsExtras.

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

Definition vec_ct `(c : A) : vec A 0 -> A := const c.
Definition vec_op1 `(f : A -> A) (a : vec A 1) : A :=
    f (a !!! 0%fin).
Definition vec_op2 `(f : A -> A -> A) (a : vec A 2) : A :=
    f (a !!! 0%fin) (a !!! 1%fin).
Definition vec_op3 `(f : A -> A -> A -> A) (a : vec A 3) : A :=
    f (a !!! 0%fin) (a !!! 1%fin) (a !!! 2%fin).
Definition vec_op4 `(f : A -> A -> A -> A -> A) (a : vec A 4) : A :=
    f (a !!! 0%fin) (a !!! 1%fin) (a !!! 2%fin) (a !!! 3%fin).

Definition vec_r0 `{A} (f : Prop) : vec A 0 -> Prop :=
    const f.
Definition vec_r1 `(f : A -> Prop) (a : vec A 1) : Prop :=
    f (a !!! 0%fin).
Definition vec_r2 `(f : A -> A -> Prop) (a : vec A 2) : Prop :=
    f (a !!! 0%fin) (a !!! 1%fin).
Definition vec_r3 `(f : A -> A -> A -> Prop) (a : vec A 3) : Prop :=
    f (a !!! 0%fin) (a !!! 1%fin) (a !!! 2%fin).
Definition vec_r4 `(f : A -> A -> A -> A -> Prop) (a : vec A 4) : Prop :=
    f (a !!! 0%fin) (a !!! 1%fin) (a !!! 2%fin) (a !!! 3%fin).

Record signature : Type := {
symbol : Type;
relation : Type;
s_arity : symbol -> nat;
r_arity : relation -> nat;
}.

Arguments s_arity {s} _: assert.
Arguments r_arity {s} _: assert.

Record structure (sigma : signature) : Type := {
support : Type;
op_interp (s : symbol sigma) : vec support (s_arity s) -> support;
rel_interp (s : relation sigma) : vec support (r_arity s) -> Prop;
}.

Arguments support {sigma} s0 : assert.
Arguments op_interp {sigma} s0 s _ : assert.
Arguments rel_interp {sigma} s0 s _ : assert.

Section sec_structure_examples.

Inductive e1_symbols := Dot1 | Zero1 | One1 .
Definition e1_s_arity (s : e1_symbols) : nat :=
match s with
| Dot1 => 2
| _ => 0
end.

Definition e1_r_arity (s : False) : nat :=
match s with
end.

Definition e1_signature : signature := {|
symbol := e1_symbols;
relation := False;
s_arity := e1_s_arity;
r_arity := e1_r_arity;
|}.

Definition e1_op_interp  (s : symbol e1_signature) : vec Z (s_arity s) -> Z :=
match s as e return (vec Z (@s_arity e1_signature e) → Z)
with
| Dot1 => vec_op2 Z.add
| Zero1 => vec_ct 2%Z
| One1 => vec_ct 7%Z
end.

Definition e1_structure : structure e1_signature := {|
support := Z;
op_interp := e1_op_interp;
rel_interp := fun s => match s with end
|}.

Inductive e2_relations := Le2.

Definition e2_r_arity : e2_relations -> nat := const 2.

Definition e2_signature : signature := {|
symbol := False;
relation := e2_relations;
s_arity := fun s => match s with end;
r_arity := e2_r_arity;
|}.

Definition e2_rel_interp (s : relation e2_signature) : vec nat (r_arity s) -> Prop :=
match s as e return (vec nat (@r_arity e2_signature e) → Prop)
with
| Le2 => vec_r2 (fun x y => x > y)
end.

Definition e2_structure : structure e2_signature := {|
support := nat;
op_interp := fun (s : symbol e2_signature) => match s with end;
rel_interp := e2_rel_interp;
|}.

Inductive e3_relation := I3 | A3 | B3.

Definition e3_signature : signature := {|
symbol := False;
relation := e3_relation;
s_arity := fun s => match s with end;
r_arity := const 1;
|}.

Inductive eq_relation := EqS.

Definition eq_signature : signature := {|
symbol := False;
relation := eq_relation;
s_arity := fun s => match s with end;
r_arity := const 2;
|}.

Inductive arith_symbol := SAdd | SMul | SS | S0.

Inductive arith_relation := RLt.

Definition arith_s_arity (s : arith_symbol) : nat :=
match s with
| SAdd => 2
| SMul => 2
| SS => 1
| S0 => 0
end.

Definition arith_r_arity : arith_relation -> nat := const 2.

Definition arith_signature : signature := {|
symbol := arith_symbol;
relation := arith_relation;
s_arity := arith_s_arity;
r_arity := arith_r_arity;
|}.


Definition nat_op_interp (s : symbol arith_signature) : vec nat (s_arity s) -> nat :=
match s as e return (vec nat (@s_arity arith_signature e) → nat)
with
| SAdd => vec_op2 Nat.add
| SMul => vec_op2 Nat.mul
| SS => vec_op1 S
| S0 => vec_ct 0
end.

Definition nat_rel_interp (s : relation arith_signature) : vec nat (r_arity s) -> Prop :=
match s as e return (vec nat (@r_arity arith_signature e) → Prop)
with
| Rlt => vec_r2 (fun x y => x < y)
end.

Definition nat_structure : structure arith_signature := {|
support := nat;
op_interp := nat_op_interp;
rel_interp := nat_rel_interp;
|}.

Definition arith_bool_op_interp (s : symbol arith_signature) : vec bool (s_arity s) -> bool :=
match s as e return (vec bool (@s_arity arith_signature e) → bool)
with
| SAdd => vec_op2 andb
| SMul => vec_op2 orb
| SS => vec_op1 negb
| S0 => vec_ct false
end.

Definition arith_bool_rel_interp (s : relation arith_signature) : vec bool (r_arity s) -> Prop :=
match s as e return (vec bool (@r_arity arith_signature e) → Prop)
with
| Rlt => vec_r2 implb
end.

Definition arith_bool_structure : structure arith_signature := {|
support := bool;
op_interp := arith_bool_op_interp;
rel_interp := arith_bool_rel_interp;
|}.

End sec_structure_examples.


Class Satisfaction (sigma : signature) (V F : Type) :=
    vsat_set : forall (M : structure sigma), F -> (V -> support M) -> Ensemble True.
#[global] Hint Mode Satisfaction ! - ! : typeclass_instances.

Section sec_satisfaction_defs.

Context `{Satisfaction}.

Definition vsat (M : structure sigma) (f : F) (v : V -> support M) : Prop :=
    vsat_set M f v ≡ top True.

Definition sat (M : structure sigma) (f : F) : Prop :=
    forall (v : V -> support M), vsat M f v.

Definition valid (f : F) : Prop :=
    forall (M : structure sigma), sat M f.

Definition satisfiable (f : F) : Prop :=
    exists (M : structure sigma), sat M f.

Definition unsatisfiable (f : F) : Prop := ~ satisfiable f.

Definition sem_ded (f g : F) : Prop :=
    forall (M : structure sigma), sat M f -> sat M g.

Definition sat_set (M : structure sigma) (Gamma : Ensemble F) :=
    forall (f : F), f ∈ Gamma -> sat M f.

Definition satisfiable_set (Gamma : Ensemble F) :=
    exists (M : structure sigma), sat_set M Gamma.

Definition unsatisfiable_set (Gamma : Ensemble F) := ~ satisfiable_set Gamma.

End sec_satisfaction_defs.

Fixpoint f_sat {sigma} `{EqDecision V} {A} (a_sat : forall (M : structure sigma), (A V) -> (V -> support M) -> Ensemble True)
    (M : structure sigma) (f : Formula V A) (v : V -> support M) :=
match f with
| Atomic a => a_sat M a v
| Bot => ∅
| Impl f g => complement (f_sat a_sat M f v) ∪ (f_sat a_sat M g v)
| All x f => indexed_intersection (fun (a : support M) => f_sat a_sat M f (fn_update v x a))
end.

#[export] Instance formula_satisfaction `{EqDecision V} `{Satisfaction sigma V (A V)} :
    Satisfaction sigma V (Formula V A) := f_sat vsat_set.

Section vsat_props.

Context {sigma : signature} `{EqDecision V} `{Satisfaction sigma V (A V)}  (M : structure sigma).

Lemma vsat_atomic : forall (a : A V) (v : V -> support M),
    vsat M (Atomic a) v <-> vsat M a v.
Proof. done. Qed.

Lemma vsat_bot : forall (v : V -> support M),
    ~ vsat M (@Bot V A) v.
Proof.
    intros; unfold vsat, vsat_set; cbn.
    by intro; apply top_not_bottom; symmetry.
Qed.

Lemma vsat_impl : forall (f g : Formula V A) (v : V -> support M),
    vsat M (Impl f g) v <-> (vsat M f v -> vsat M g v).
Proof.
    intros; unfold vsat; cbn.
    rewrite !top_char, elem_of_union, elem_of_complement.
    split.
    - by intros [] ?.
    - intros Himpl.
      destruct (classic (I ∈ vsat_set M f v)); [| by left].
      by right; apply Himpl.
Qed.

Lemma vsat_all : forall (x : V) (f : Formula V A) (v : V -> support M),
    vsat M (All x f) v <-> forall a, vsat M f (fn_update v x a).
Proof.
    intros; unfold vsat; cbn.
    setoid_rewrite top_char.
    by rewrite elem_of_indexed_intersection.
Qed.

Lemma vsat_top : forall (v : V -> support M),
    vsat M (@f_top V A) v.
Proof. by intros; apply vsat_impl. Qed.

Lemma vsat_neg : forall (f : Formula V A) (v : V -> support M),
    vsat M (f_neg f) v <-> ~ vsat M f v.
Proof.
    intros; unfold f_neg; rewrite vsat_impl; split.
    - intros Hneg Hf.
      by eapply vsat_bot, Hneg.
    - by intros ? ?.
Qed.

Lemma vsat_and : forall (f g: Formula V A) (v : V -> support M),
    vsat M (f_and f g) v <-> vsat M f v /\ vsat M g v.
Proof.
    intros; unfold f_and.
    rewrite vsat_neg, vsat_impl, vsat_neg.
    by tauto.
Qed.

Lemma vsat_or : forall (f g: Formula V A) (v : V -> support M),
    vsat M (f_or f g) v <-> vsat M f v \/ vsat M g v.
Proof.
    intros; unfold f_or.
    rewrite vsat_impl, vsat_neg.
    by tauto.
Qed.

Lemma vsat_iff : forall (f g: Formula V A) (v : V -> support M),
    vsat M (f_iff f g) v <-> (vsat M f v <-> vsat M g v).
Proof.
    intros; unfold f_iff.
    rewrite vsat_and, !vsat_impl.
    by tauto.
Qed.

Lemma vsat_ex : forall (x : V) (f : Formula V A) (v : V -> support M),
    vsat M (f_ex x f) v <-> exists (a : support M), vsat M f (fn_update v x a).
Proof.
    intros; unfold f_ex.
    rewrite vsat_neg, vsat_all.
    setoid_rewrite vsat_neg.
    split.
    - by intro; apply not_all_not_ex.
    - intros [z Hz] Hall.
      by eapply Hall.
Qed.

End vsat_props.


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
    vterm_rect V (fun _ => listset V) (fun _ _ => list (listset V))
      (fun v => {[v]})
      (fun _ _ ls => ⋃ ls)
      []
      (fun _ _ vt _ vts =>  vt :: vts).

Definition Term : Type := VTerm False.

Definition term_to_vterm (V : Type) : Term -> VTerm V :=
    vterm_rect False (fun _ => VTerm V) (fun n _ => vec (VTerm V) n)
      (fun x => match x with end)
      (fun sigma _ va => App sigma va)
      [#]
      (fun _ n v0 _ vl => v0 ::: vl).

Lemma term_vars : forall (t : Term), vterm_vars t ≡ ∅.
Proof.
    induction t using vterm_ind; cbn; [by inversion v |].
    apply empty_union_list, Forall_forall; intros.
    by rewrite elem_of_equiv_empty; intro.
Qed.

Definition vterm_eval (A : structure sigma) `(v : V -> support A) :
    VTerm V -> support A :=
    vterm_rect V (fun _ => support A) (fun n _ => vec (support A) n)
      (fun x => v x)
      (fun sigma _ va => op_interp A sigma va)
      [#]
      (fun _ n v0 _ vl => v0 ::: vl).

Definition term_eval (A : structure sigma) : Term -> support A :=
    vterm_eval A (fun (v : False) => match v with end).

Inductive RelAtom (V : Type) :=
| RApp (pi : relation sigma) (t : vec (VTerm V) (r_arity pi)).

Inductive EqAtom (V : Type) :=
| REq (l r : VTerm V).

Inductive RelEqAtom (V : Type) :=
| ARel (ar : RelAtom V)
| AEq (ae : EqAtom V).

Definition RelFormula (V : Type) := Formula V RelAtom.

Definition RelEqFormula (V : Type) := Formula V RelEqAtom.

Definition eq_set_vsat {V} (A : structure sigma) (e : EqAtom V) `(v : V -> support A) :
    Ensemble True :=
match e with
| REq _ l r => const (vterm_eval A v l = vterm_eval A v r)
end.

#[export] Instance eq_atom_satisfaction V : Satisfaction sigma V (EqAtom V) :=
    eq_set_vsat.

Definition rel_set_vsat {V} (A : structure sigma) (e : RelAtom V) `(v : V -> support A) : Ensemble True :=
match e with
| RApp _ pi ts => const (rel_interp A pi (vmap (vterm_eval A v) ts))
end.

#[export] Instance rel_atom_satisfaction V : Satisfaction sigma V (RelAtom V) :=
    rel_set_vsat.

End sec_terms.
