From stdpp Require Import prelude.
From Coq Require Import Classical.

From sets Require Import Ensemble Functions.

From Semantics.Utils Require Import SetsExtras.
From Semantics.FOL Require Import Syntax.

Record structure (sigma : signature) : Type := {
support : Type;
op_interp (s : symbol sigma) : vec support (s_arity s) -> support;
rel_interp (s : relation sigma) : Ensemble (vec support (r_arity s));
}.

Arguments support {sigma} s0 : assert.
Arguments op_interp {sigma} s0 s _ : assert.
Arguments rel_interp {sigma} s0 s _ : assert.

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

#[export] Instance structure_inhabited `{EnsuringInhabitation sigma} :
    forall (M : structure sigma), Inhabited (support M).
Proof.
    destruct ensures_inhabitation as [s Hs]; intro M.
    econstructor.
    eapply (op_interp M s).
    rewrite Hs.
    by constructor.
Qed.

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

#[export] Instance sat_set_proper : Proper ((=) ==> (⊆) ==> flip impl) sat_set.
Proof.
    intros A A' -> Gamma Delta Hincl HGamma f Hf.
    by apply HGamma, Hincl.
Qed.

#[export] Instance unsatisfiable_set_proper : Proper ((⊆) ==> impl) unsatisfiable_set.
Proof.
    intros Delta Gamma Hincl HDelta [M HGamma].
    by apply HDelta; exists M; rewrite Hincl.
Qed.

Definition set_sem_ded (Gamma : Ensemble F) (f : F) : Prop :=
    forall (M : structure sigma), sat_set M Gamma -> sat M f.


#[export] Instance set_sem_ded_proper : Proper ((⊆) ==> (=) ==> impl) set_sem_ded.
Proof.
    intros Delta Gamma Hincl _ f -> HDelta A HGamma.
    by apply HDelta; rewrite Hincl.
Qed.

End sec_satisfaction_defs.

Class FreeVarsSupportedSatisfaction (sigma : signature) (V F : Type) `{Satisfaction sigma V F} `{FreeVars F V} : Prop :=
    fv_supported_sat :
        forall (M : structure sigma) (f : F) (v1 v2 : V -> support M),
        (forall (x : V), x ∈ free_vars f -> v1 x = v2 x) ->
        vsat M f v1 <-> vsat M f v2.

Section sec_fv_supp_sat_props.

Context `{FreeVarsSupportedSatisfaction}.

Lemma fv_supported_sat_statement_all :
    forall (M : structure sigma) (f : F), f ∈ statement F ->
    forall (v1 v2 : V -> support M), vsat M f v1 <-> vsat M f v2.
Proof.
    intros * Hf *.
    apply fv_supported_sat.
    intros x Hx.
    by apply Hf in Hx; set_solver.
Qed.

Lemma fv_supported_sat_statement_exists :
    forall (M : structure sigma) `{Inhabited (support M)} (f : F), f ∈ statement F ->
    sat M f <-> exists (v : V -> support M), vsat M f v.
Proof.
    intros; split.
    - by intros Hsat; exists (const inhabitant); apply Hsat.
    - by intros [v Hvsat] v'; eapply fv_supported_sat_statement_all.
Qed.

End sec_fv_supp_sat_props.

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

#[export] Instance formula_fv_supp_sat `{EqDecision V}
    `{FreeVarsSupportedSatisfaction sigma V (A V)} : FreeVarsSupportedSatisfaction sigma V (Formula V A).
Proof.
    intro M; induction f; intros * Heqv.
    - cbn; unfold vsat, vsat_set, formula_satisfaction, f_sat.
      by apply fv_supported_sat.
    - done.
    - rewrite !vsat_impl, IHf1, IHf2; [done |..].
      + by intros; apply Heqv, elem_of_union; right.
      + by intros; apply Heqv, elem_of_union; left.
    - rewrite !vsat_all.
      apply forall_proper; intro a.
      apply IHf.
      intros y Hy.
      unfold fn_update; case_decide; [by subst |].
      apply Heqv, elem_of_difference.
      split; [done |].
      by rewrite elem_of_singleton.
Qed.

Lemma unsatisfiable_set_bot `{EnsuringInhabitation sigma} `{EqDecision V}  `{Satisfaction sigma V (A V)} :
    forall (Gamma : Ensemble (Formula V A)),
        unsatisfiable_set (sigma := sigma) Gamma <-> set_sem_ded (sigma := sigma) Gamma Bot.
Proof.
    intros; split.
    - intros Hunsat M HGamma.
      unfold unsatisfiable_set in Hunsat.
      by contradict Hunsat; eexists.
    - intros Hbot [M HGamma].
      apply Hbot in HGamma.
      specialize (HGamma (const inhabitant)).
      contradict HGamma.
      apply vsat_bot.
Qed.

Lemma set_sem_ded_by_unsatisfiability `{EnsuringInhabitation sigma} `{EqDecision V}  `{FreeVarsSupportedSatisfaction sigma V (A V)} :
    forall (Gamma : Ensemble (Formula V A)) (f : Formula V A),
    f ∈ statement (Formula V A) ->
    set_sem_ded (sigma := sigma) Gamma f
      <->
    unsatisfiable_set (sigma := sigma) (Gamma ∪ {[f_neg f]}).
Proof.
    intros * Hf; split.
    - intros HGammaf [M HGamma'].
      apply (sat_set_proper M M eq_refl Gamma ) in HGamma' as HGamma;
        [| by set_solver].
      apply (sat_set_proper M M eq_refl {[f_neg f]}) in HGamma' as Hnegf;
        [| by set_solver].
      apply HGammaf in HGamma.
      specialize (HGamma (const inhabitant)).
      contradict HGamma.
      by apply vsat_neg, Hnegf, elem_of_singleton.
    - unfold unsatisfiable_set. intros Hunsat M HGamma v.
      destruct (classic (vsat M f v)) as [| Hneg]; [done |].
      apply vsat_neg in Hneg.
      contradict Hunsat.
      exists M; intro g; rewrite elem_of_union, elem_of_singleton.
      intros [Hg | ->]; [by apply HGamma |].
      apply fv_supported_sat_statement_exists; [by typeclasses eauto | | by eexists].
      apply equiv_empty; cbn.
      assert (free_vars f ≡ ∅) by apply Hf.
      by set_solver.
Qed.

Section sec_formula_eval.

Context
    {sigma : signature}.

Definition vterm_eval (A : structure sigma) `(v : V -> support A) :
    VTerm sigma V -> support A :=
    vterm_rect sigma V (fun _ => support A) (fun n _ => vec (support A) n)
      (fun x => v x)
      (fun sigma _ va => op_interp A sigma va)
      [#]
      (fun _ n v0 _ vl => v0 ::: vl).

Lemma vterm_eval_var (A : structure sigma) `(v : V -> support A) :
    forall (x : V), vterm_eval A v (Var x) = v x.
Proof. done. Qed.

Lemma vterm_eval_app (A : structure sigma) `(v : V -> support A) :
    forall (s : symbol sigma) (ts : vec (VTerm sigma V) (s_arity s)),
    vterm_eval A v (App s ts) = op_interp A s (vmap (vterm_eval A v) ts).
Proof. done. Qed.

Definition term_eval (A : structure sigma) : GroundTerm sigma -> support A :=
    vterm_eval A (fun (v : False) => match v with end).

Lemma vterm_eval_fv :
    forall V (A : structure sigma) (t : VTerm sigma V) (v1 v2 : V -> support A),
    (forall (x : V), x ∈ free_vars t -> v1 x = v2 x) ->
    vterm_eval A v1 t = vterm_eval A v2 t.
Proof.
    intros * Heqv; induction t as [| ? ? Hind] using vterm_ind.
    - by apply Heqv, elem_of_singleton.
    - rewrite !vterm_eval_app; f_equal.
      apply vec_eq; intro i.
      rewrite !vlookup_map.
      rewrite Forall_vlookup in Hind.
      apply Hind.
      intros x Hx.
      apply Heqv.
      rewrite vterm_fv_app.
      apply elem_of_union_list.
      exists (free_vars (l !!! i)); split; [| done].
      rewrite vec_to_list_map, elem_of_list_fmap.
      exists (l !!! i); split; [done |].
      by apply elem_of_vlookup; eexists.
Qed.

Definition eq_vsat_set {V}
    (A : structure sigma) (e : EqAtom sigma V) (v : V -> support A) : Ensemble True :=
match e with
| REq l r => const (vterm_eval A v l = vterm_eval A v r)
end.

#[export] Instance eq_atom_satisfaction V : Satisfaction sigma V (EqAtom sigma V) :=
    eq_vsat_set.

Lemma vsat_eq : forall V (A : structure sigma) (l r : VTerm sigma V) (v : V -> support A),
    vsat A (REq l r) v <-> vterm_eval A v l = vterm_eval A v r.
Proof.
    unfold vsat, vsat_set, eq_atom_satisfaction, eq_vsat_set.
    by intros; rewrite top_char.
Qed.

#[export] Instance eq_atom_fv_supp_sat V : FreeVarsSupportedSatisfaction sigma V (EqAtom sigma V).
Proof.
    intros M [] v1 v2 Heqv.
    rewrite !vsat_eq.
    cbn in Heqv.
    rewrite vterm_eval_fv with (t := l) (v2 := v2),
      vterm_eval_fv with (t := r) (v2 := v2); [done |..].
    - by intros; apply Heqv; set_solver.
    - by intros; apply Heqv; set_solver.
Qed.

Definition rel_vsat_set {V}
    (A : structure sigma) (e : RelAtom sigma V) `(v : V -> support A) : Ensemble True :=
match e with
| RApp pi ts => const (rel_interp A pi (vmap (vterm_eval A v) ts))
end.

#[export] Instance rel_atom_satisfaction V : Satisfaction sigma V (RelAtom sigma V) :=
    rel_vsat_set.

Lemma vsat_rel : forall V (A : structure sigma)
    (pi : relation sigma) (ts : vec (VTerm sigma V) (r_arity pi)) (v : V -> support A),
    vsat A (RApp pi ts) v <-> vmap (vterm_eval A v) ts ∈ rel_interp A pi.
Proof.
    unfold vsat, vsat_set, eq_atom_satisfaction, eq_vsat_set.
    by intros; rewrite top_char.
Qed.

#[export] Instance rel_atom_fv_supp_sat V : FreeVarsSupportedSatisfaction sigma V (RelAtom sigma V).
Proof.
    intros M [] v1 v2 Heqv.
    rewrite !vsat_rel.
    replace (vmap (vterm_eval M v2) t) with (vmap (vterm_eval M v1) t); [done |].
    apply vec_eq; intro i.
    rewrite !vlookup_map.
    apply vterm_eval_fv; intros x Hx.
    apply Heqv.
    cbn; apply elem_of_union_list; eexists; split; [| done].
    apply elem_of_list_fmap; eexists; split; [done |].
    by apply elem_of_vlookup; eexists.
Qed.

Definition rel_eq_vsat_set {V}
    (A : structure sigma) (e : RelEqAtom sigma V) `(v : V -> support A) : Ensemble True :=
match e with
| ARel ar => vsat_set A ar v
| AEq ae => vsat_set A ae v
end.

#[export] Instance rel_eq_atom_satisfaction V : Satisfaction sigma V (RelEqAtom sigma V) :=
    rel_eq_vsat_set.

#[export] Instance rel_eq_atom_fv_supp_sat V : FreeVarsSupportedSatisfaction sigma V (RelEqAtom sigma V).
Proof.
    intros M [] v1 v2 Heqv.
    - by apply rel_atom_fv_supp_sat.
    - by apply eq_atom_fv_supp_sat.
Qed.

End sec_formula_eval.

