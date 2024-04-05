From stdpp Require Import prelude.
From sets Require Import Ensemble.

From Semantics.Utils Require Import SetsExtras.
From Semantics.FOL Require Import Syntax Semantics.
From Semantics.PROLOG Require Import Syntax.

Section sec_prolog.

Context
    (sigma : signature).

Lemma vsat_definite_clause :
    forall `{EqDecision V} (A : structure sigma) (cl : definite_clause sigma V) (v : V -> support A),
    vsat A (definite_clause_to_rel_formula cl) v
      <->
    (Forall (fun a => vsat A a v) (get_ra_conjunction (cl_body cl)) -> vsat A (cl_head cl) v).
Proof.
    intros; unfold definite_clause_to_rel_formula. setoid_rewrite vsat_impl.
    cut ((vsat A (ra_conjunction_to_rel_formula (cl_body cl)) v
        <->
        (Forall (λ a : RelAtom sigma V, vsat A a v) (get_ra_conjunction (cl_body cl)))));
      [by intros -> |].
    unfold ra_conjunction_to_rel_formula; cbn.
    setoid_rewrite vsat_list_and; rewrite! Forall_forall.
    split; intros Hall f Hf.
    - cut (vsat A (Atomic f) v); [done |].
      by apply Hall, elem_of_list_fmap; eexists.
    - apply elem_of_list_fmap in Hf as [a  [-> Ha]].
      by apply Hall.
Qed.

Lemma vsat_definite_goal :
    forall `{EqDecision V} (A : structure sigma) `{Inhabited (support A)} (cl : definite_goal sigma V),
    sat A (definite_goal_to_rel_formula cl)
      <->
    exists (v : V -> support A),
      Forall (fun f => vsat A f v) (get_ra_conjunction (get_definite_goal cl)).
Proof.
    intros ? ? A ? [[atoms]]; cbn.
    unfold definite_goal_to_rel_formula, get_definite_goal, ra_conjunction_to_rel_formula; cbn.
    rewrite (sat_ex_closure A (f_list_and (map Atomic atoms))).
    apply exist_proper; intro v.
    rewrite vsat_list_and, !Forall_forall.
    split; intros Hall x Hx.
    - by apply (Hall (Atomic x)), elem_of_list_fmap; eexists.
    - apply elem_of_list_fmap in Hx as [a [-> Ha]].
      by apply Hall.
Qed.

Lemma set_sem_ded_by_unsatisfiability_pgm_query `{EnsuringInhabitation sigma} `{EqDecision V}:
    forall `(pgm : program sigma V) (q : query sigma V) (pgm_set := list_to_set (map definite_clause_to_rel_formula pgm)),
    set_sem_ded (sigma := sigma) pgm_set (definite_goal_to_rel_formula q)
      <->
    unsatisfiable_set (sigma := sigma) (pgm_set ∪ {[definite_goal_negation_to_rel_formula (negate_definite_goal q)]}).
Proof.
    intros; unfold definite_goal_to_rel_formula.
    rewrite (set_sem_ded_by_unsatisfiability_ex_closure pgm_set).
    apply unsatisfiable_set_eqv; intros M _.
    unfold definite_goal_negation_to_rel_formula, finite_disjunction_to_formula.
    unfold get_definite_goal, ra_conjunction_to_rel_formula; cbn.
    rewrite sat_neg_list_and; cbn.
    destruct q; cbn.
    replace (map f_neg (map Atomic (get_ra_conjunction get_definite_goal)))
      with (map (f_neg ∘ Atomic) (get_ra_conjunction get_definite_goal)); [done |].
    generalize (get_ra_conjunction get_definite_goal); induction l; [done |].
    by cbn; rewrite IHl.
Qed.

End sec_prolog.


Section sec_Herbrand_model.

Definition herbrand_base (sig : signature) : Type :=
    RelAtom sig False.

Context
    {sig : signature} `{!EnsuringInhabitation sig}.


Definition ground_term_rel_interp (J : Ensemble (herbrand_base sig))
    (r : relation sig) : Ensemble (vec (GroundTerm sig) (r_arity r)) :=
    fun ts => RApp r ts ∈ J.

Definition herbrand_structure (J : Ensemble (herbrand_base sig)) : structure sig :=
{|
support := GroundTerm sig;
op_interp := App;
rel_interp := ground_term_rel_interp J;
|}.

Lemma herbrand_structure_vterm_eval :
    forall (J : Ensemble (herbrand_base sig)) (t : GroundTerm sig) (v : False -> GroundTerm sig),
    vterm_eval (herbrand_structure J) v t = t.
Proof.
    intros;  induction t as [|? ? Hind] using vterm_ind; [by inversion v0 |].
    rewrite vterm_eval_app.
    unfold op_interp, herbrand_structure at 1; f_equal.
    apply vec_eq; intro i; rewrite vlookup_map.
    by rewrite Forall_vlookup in Hind; apply Hind.
Qed.

Lemma herbrand_structure_vec_vterm_eval :
    forall (J : Ensemble (herbrand_base sig)) (v : False -> GroundTerm sig)
        (n : nat) (ts : vec (GroundTerm sig) n),
    vmap (vterm_eval (herbrand_structure J) v) ts = ts.
Proof.
    intros; apply vec_eq; intro i; rewrite vlookup_map.
    by apply herbrand_structure_vterm_eval.
Qed.

Lemma herbrand_structure_base_satisfaction :
    forall (J : Ensemble (herbrand_base sig)) (f : herbrand_base sig),
    sat (herbrand_structure J) f <-> f ∈ J.
Proof.
    intros.
    unfold sat, vsat, vsat_set, rel_atom_satisfaction, rel_vsat_set.
    destruct f; cbn.
    setoid_rewrite top_char.
    unfold elem_of at 1, pow_set_elem_of; cbn.
    unfold ground_term_rel_interp.
    split.
    - intros Hsat.
      specialize (Hsat (fun x => match x with end)).
      replace (vmap _ t) with t in Hsat; [done |].
      by symmetry; apply herbrand_structure_vec_vterm_eval.
    - intros Hf v.
      replace (vmap _ t) with t; [done |].
      by symmetry; apply herbrand_structure_vec_vterm_eval.
Qed.

Definition structure_projection_on_herbrand_base
    (A : structure sig) : Ensemble (herbrand_base sig) :=
    fun f => sat A f.

End sec_Herbrand_model.
