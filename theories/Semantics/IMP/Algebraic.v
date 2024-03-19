From stdpp Require Import prelude.
From Coq Require Import FunctionalExtensionality.
From sets Require Import Ensemble.
From Semantics Require Import Syntax State Denotational.

Record signature : Type := {
sort : Type;
symbols : Type;
result_sort : symbols -> sort;
arity : symbols -> { n : nat & fin n -> sort};
}.

Arguments result_sort {s} _: assert.
Arguments arity {s} _: assert.

Definition support_star_helper `(support : sort Sigma -> Type)
    `(ar : fin n -> sort Sigma) : Type :=
    forall (i : fin n), support (ar i).

Record algebra (Sigma : signature) : Type := {
support : sort Sigma -> Type;
support_star `(ar : fin n -> sort Sigma) : Type :=
    support_star_helper support ar;
op_interp :
    forall (sigma : symbols Sigma)
        (tuple : support_star (projT2 (arity sigma))),
        support (result_sort sigma);
}.

Arguments support {Sigma} a _ : assert.
Arguments support_star {Sigma} a {n}%nat_scope ar%function_scope : assert.
Arguments op_interp {Sigma} a sigma tuple : assert.

Section sec_sigma_algebra.

Context
  {Sigma : signature}.

Definition algebra_fn (A B : algebra Sigma): Type :=
    forall (s : sort Sigma), support A s -> support B s.

Definition algebra_fn_id (A : algebra Sigma): algebra_fn A A :=
    fun (s : sort Sigma) => id.

Definition algebra_fn_compose {A B C : algebra Sigma}
    (g : algebra_fn B C) (f : algebra_fn A B) : algebra_fn A C :=
    fun (s : sort Sigma) => g s ∘ f s.

Lemma algebra_fn_compose_id_left:
    forall (A B : algebra Sigma) (f : algebra_fn A B),
    algebra_fn_compose (algebra_fn_id B) f = f.
Proof. done. Qed.

Lemma algebra_fn_compose_id_right:
    forall (A B : algebra Sigma) (f : algebra_fn A B),
    algebra_fn_compose f (algebra_fn_id A) = f.
Proof. done. Qed.

Lemma algebra_fn_compose_assoc: forall (A B C D : algebra Sigma)
    (f : algebra_fn A B) (g : algebra_fn B C) (h : algebra_fn C D),
    algebra_fn_compose h (algebra_fn_compose g f)
      =
    algebra_fn_compose (algebra_fn_compose h g) f.
Proof. done. Qed.

Definition algebra_fn_star `(f : algebra_fn A B) `{ar : fin n -> sort Sigma}
  (a_star : support_star A ar): support_star B ar :=
  fun i => (f (ar i) (a_star i)).

Class AlgebraMorphism `(f : algebra_fn A B): Prop :=
  algebra_morphism : forall (sigma : symbols Sigma) (a_star : support_star A (projT2 (arity sigma))),
    f (result_sort sigma) (op_interp A sigma a_star)
      =
    op_interp B sigma (algebra_fn_star f a_star).

#[export] Instance algebra_fn_id_morphism:
    forall (A : algebra Sigma), AlgebraMorphism (algebra_fn_id A).
Proof. done. Qed.

#[export] Instance algebra_fn_compose_morphism:
    forall (A B C : algebra Sigma) (g : algebra_fn B C) (f : algebra_fn A B),
    AlgebraMorphism f -> AlgebraMorphism g ->
    AlgebraMorphism (algebra_fn_compose g f).
Proof.
    intros * Hf Hg ? ?; unfold algebra_fn_compose at 1; cbn.
    by rewrite Hf, Hg.
Qed.

Class AlgebraIso `(f : algebra_fn A B) (g : algebra_fn B A) : Prop :=
{
    f_morphism :> AlgebraMorphism f;
    g_morphism :> AlgebraMorphism g;
    algebra_iso_A : algebra_fn_compose g f = algebra_fn_id A;
    algebra_iso_B : algebra_fn_compose f g = algebra_fn_id B;
}.

Class Initial (A : algebra Sigma) : Prop :=
    initiality :
      forall (B : algebra Sigma), exists! (f : algebra_fn A B), AlgebraMorphism f.

#[export] Instance equiv_algebra : Equiv (algebra Sigma) :=
    fun A B => exists (f : algebra_fn A B) (g : algebra_fn B A), AlgebraIso f g.

Lemma initial_algebras_iso:
    forall (A B : algebra Sigma), Initial A -> Initial B -> A ≡ B.
Proof.
    intros A B HA HB.
    destruct (HA B) as (f & Hf & _).
    destruct (HB A) as (g & Hg & _).
    exists f, g; split; [done | done |..].
    - destruct (HA A) as (ida & Hida & Hunida).
      rewrite <- (Hunida (algebra_fn_id A)) by typeclasses eauto.
      by symmetry; apply Hunida; typeclasses eauto.
    - destruct (HB B) as (idb & Hidb & Hunidb).
      rewrite <- (Hunidb (algebra_fn_id B)) by typeclasses eauto.
      by symmetry; apply Hunidb; typeclasses eauto.
Qed.

Lemma Initial_proper_impl : Proper ((≡) ==> impl) Initial.
Proof.
    intros A A' (f & g & []) HA B.
    destruct (HA B) as (h & Hh & Hunih).
    exists (algebra_fn_compose h g); split; [by typeclasses eauto |].
    intros h' Hh'.
    rewrite (Hunih (algebra_fn_compose h' f)) by typeclasses eauto.
    by rewrite <- algebra_fn_compose_assoc, algebra_iso_B0.
Qed.

End sec_sigma_algebra.

Section sec_IMP_algebra.

Context `{EqDecision L}.

Inductive imp_sort : Type := is_A | is_B | is_C.

Inductive imp_symbols : Type :=
(* arithmetic exps *)
| is_int : Z -> imp_symbols
| is_var : L -> imp_symbols
| is_plus
| is_minus
| is_mul
(* arithmetic comparators *)
| is_eq
| is_le
(* boolean exps *)
| is_true
| is_false
| is_not
| is_and
| is_or
(* commands *)
| is_skip
| is_asgn : L -> imp_symbols
| is_seq
| is_if
| is_while
.

Definition imp_symbols_result (sigma : imp_symbols) : imp_sort :=
match sigma with
| is_int _ => is_A
| is_var _ => is_A
| is_plus => is_A
| is_minus => is_A
| is_mul => is_A
| is_eq => is_B
| is_le => is_B
| is_true => is_B
| is_false => is_B
| is_not => is_B
| is_and => is_B
| is_or => is_B
| is_skip => is_C
| is_asgn _ => is_C
| is_seq => is_C
| is_if => is_C
| is_while => is_C
end.

Definition zero_fn {T : Type} (a : fin 0) : T :=
    fin_0_inv _ a.

Definition zero_dep_fn {T : fin 0 -> Type} : forall (a : fin 0), T a :=
    fin_0_inv _.

Definition if_arity : {n : nat & fin n -> imp_sort} :=
    existT 3 (fun i =>
    match i with
    | 0%fin => is_B
    | _ => is_C
    end).

Definition while_arity : {n : nat & fin n -> imp_sort} :=
    existT 2 (fun i =>
    match i with
    | 0%fin => is_B
    | _ => is_C
    end).

Definition imp_symbols_arity (sigma : imp_symbols) : {n : nat & fin n -> imp_sort} :=
match sigma with
| is_int _ => existT 0 zero_fn
| is_var _ => existT 0 zero_fn
| is_plus => existT 2 (const is_A)
| is_minus => existT 2 (const is_A)
| is_mul => existT 2 (const is_A)
| is_eq => existT 2 (const is_A)
| is_le => existT 2 (const is_A)
| is_true => existT 0 zero_fn
| is_false => existT 0 zero_fn
| is_not => existT 1 (const is_B)
| is_and => existT 2 (const is_B)
| is_or => existT 2 (const is_B)
| is_skip => existT 0 zero_fn
| is_asgn _ => existT 1 (const is_A)
| is_seq => existT 2 (const is_C)
| is_if => if_arity
| is_while => while_arity
end.

Definition IMP_sign : signature :=
{|
    sort := imp_sort;
    symbols := imp_symbols;
    result_sort := imp_symbols_result;
    arity := imp_symbols_arity;
|}.

Definition IMP_term_support (s : sort IMP_sign) : Type :=
match s with
| is_A => AExp L
| is_B => BExp L
| is_C => Cmd L
end.

Definition IMP_term_op_interp (sigma : symbols IMP_sign)
    (tuple : support_star_helper IMP_term_support (projT2 (arity sigma))) :
    IMP_term_support (result_sort sigma) :=
match sigma as i
    return
        (support_star_helper IMP_term_support (projT2 (@arity IMP_sign i)) ->
        IMP_term_support (@result_sort IMP_sign i))
with
| is_int z => fun _ => AVal z
| is_var n => fun _ => Var n
| is_plus => fun tuple => Plus (tuple 0%fin) (tuple 1%fin)
| is_minus => fun tuple => Minus (tuple 0%fin) (tuple 1%fin)
| is_mul => fun tuple => Mul (tuple 0%fin) (tuple 1%fin)
| is_eq => fun tuple => AEq (tuple 0%fin) (tuple 1%fin)
| is_le => fun tuple => ALe (tuple 0%fin) (tuple 1%fin)
| is_true => fun _ => BVal true
| is_false => fun _ => BVal false
| is_not => fun tuple => Not (tuple 0%fin)
| is_and => fun tuple => And (tuple 0%fin) (tuple 1%fin)
| is_or => fun tuple => Or (tuple 0%fin) (tuple 1%fin)
| is_skip => fun _ => Skip
| is_asgn n => fun tuple => Asgn n (tuple 0%fin)
| is_seq => fun tuple => Seq (tuple 0%fin) (tuple 1%fin)
| is_if => fun tuple => If (tuple 0%fin) (tuple 1%fin) (tuple 2%fin)
| is_while => fun tuple => While (tuple 0%fin) (tuple 1%fin)
end
  tuple.

Definition IMP_term_algebra : algebra IMP_sign :=
{|
    support := IMP_term_support;
    op_interp := IMP_term_op_interp;
|}.

Section sec_term_interp.

Context
    (A : algebra IMP_sign).

Fixpoint IMP_term_interp_a (a : AExp L) : support A is_A :=
match a with
| AVal n => op_interp A (is_int n) (fin_0_inv _)
| Var x => op_interp A (is_var x) (fin_0_inv _)
| Plus a1 a2 =>
    op_interp A is_plus
        (fun i =>
            match i with
            | 0%fin => IMP_term_interp_a a1
            | _ => IMP_term_interp_a a2
            end)
| Minus a1 a2 =>
    op_interp A is_minus
        (fun i =>
            match i with
            | 0%fin => IMP_term_interp_a a1
            | _ => IMP_term_interp_a a2
            end)
| Mul a1 a2 =>
    op_interp A is_mul
        (fun i =>
            match i with
            | 0%fin => IMP_term_interp_a a1
            | _ => IMP_term_interp_a a2
            end)
end.

Fixpoint IMP_term_interp_b (b : BExp L) : support A is_B :=
match b with
| BVal true => op_interp A is_true (fin_0_inv _)
| BVal false => op_interp A is_false (fin_0_inv _)
| AEq a1 a2 =>
    op_interp A is_eq
        (fun i =>
            match i with
            | 0%fin => IMP_term_interp_a a1
            | _ => IMP_term_interp_a a2
            end)
| ALe a1 a2 =>
    op_interp A is_le
        (fun i =>
            match i with
            | 0%fin => IMP_term_interp_a a1
            | _ => IMP_term_interp_a a2
            end)
| Not b => op_interp A is_not (const (IMP_term_interp_b b))
| And b1 b2 =>
    op_interp A is_and
        (fun i =>
            match i with
            | 0%fin => IMP_term_interp_b b1
            | _ => IMP_term_interp_b b2
            end)
| Or b1 b2 =>
    op_interp A is_or
        (fun i =>
            match i with
            | 0%fin => IMP_term_interp_b b1
            | _ => IMP_term_interp_b b2
            end)
end.


Definition support_star_if (b : support A is_B) (c1 c2 : support A is_C) :
    support_star A (projT2 (@arity IMP_sign is_if)).
Proof.
  intro i; inv_fin i; [exact b |].
  intro i; inv_fin i; [exact c1 |].
  intro i; inv_fin i; [exact c2 |].
  intro i; inv_fin i.
Defined.

Definition support_star_while (b : support A is_B) (c : support A is_C) :
    support_star A (projT2 (@arity IMP_sign is_while)).
Proof.
  intro i; inv_fin i; [exact b |].
  intro i; inv_fin i; [exact c |].
  intro i; inv_fin i.
Defined.

Fixpoint IMP_term_interp_c (c : Cmd L) : support A is_C :=
match c with
| Skip => op_interp A is_skip (fin_0_inv _)
| Asgn x a => op_interp A (is_asgn x) (const (IMP_term_interp_a a))
| Seq c1 c2 =>
    op_interp A is_seq
        (fun i =>
            match i with
            | 0%fin => IMP_term_interp_c c1
            | _ => IMP_term_interp_c c2
            end)
| If b c1 c2 =>
    op_interp A is_if (support_star_if (IMP_term_interp_b b) (IMP_term_interp_c c1) (IMP_term_interp_c c2))
| While b c =>
    op_interp A is_while (support_star_while (IMP_term_interp_b b) (IMP_term_interp_c c))
end.

Definition IMP_term_interp : algebra_fn IMP_term_algebra A :=
fun s : sort IMP_sign =>
match s as i return (support IMP_term_algebra i → support A i) with
| is_A => IMP_term_interp_a
| is_B => IMP_term_interp_b
| is_C => IMP_term_interp_c
end.

#[export] Instance IMP_term_interp_morphism : AlgebraMorphism IMP_term_interp.
Proof.
  intros [] astar; cbn in *.
  - by f_equal; extensionality i; inv_fin i.
  - by f_equal; extensionality i; inv_fin i.
  - f_equal. extensionality i; inv_fin i; [done | ].
    intro i; inv_fin i; [done |].
    by intro i; inv_fin i.
  - f_equal. extensionality i; inv_fin i; [done | ].
    intro i; inv_fin i; [done |].
    by intro i; inv_fin i.
  - f_equal. extensionality i; inv_fin i; [done | ].
    intro i; inv_fin i; [done |].
    by intro i; inv_fin i.
  - f_equal. extensionality i; inv_fin i; [done | ].
    intro i; inv_fin i; [done |].
    by intro i; inv_fin i.
  - f_equal. extensionality i; inv_fin i; [done | ].
    intro i; inv_fin i; [done |].
    by intro i; inv_fin i.
  - by f_equal; extensionality i; inv_fin i.
  - by f_equal; extensionality i; inv_fin i.
  - f_equal. extensionality i; inv_fin i; [done | ].
    by intro i; inv_fin i.
  - f_equal. extensionality i; inv_fin i; [done | ].
    intro i; inv_fin i; [done |].
    by intro i; inv_fin i.
  - f_equal. extensionality i; inv_fin i; [done | ].
    intro i; inv_fin i; [done |].
    by intro i; inv_fin i.
  - by f_equal; extensionality i; inv_fin i.
  - f_equal. extensionality i; inv_fin i; [done | ].
    by intro i; inv_fin i.
  - f_equal. extensionality i; inv_fin i; [done | ].
    intro i; inv_fin i; [done |].
    by intro i; inv_fin i.
  - f_equal. extensionality i; inv_fin i; [done | ].
    intro i; inv_fin i; [done |].
    intro i; inv_fin i; [done |].
    by intro i; inv_fin i.
  - f_equal. extensionality i; inv_fin i; [done | ].
    intro i; inv_fin i; [done |].
    by intro i; inv_fin i.
Qed.

End sec_term_interp.

Definition a_1 (a1 : AExp L) : forall i : fin 1, support IMP_term_algebra (const is_A i).
Proof.
  intro i; inv_fin i; [exact a1 |].
  intro i; inv_fin i.
Defined.

Definition a_2 (a1 a2 : AExp L) : forall i : fin 2, support IMP_term_algebra (const is_A i).
Proof.
  intro i; inv_fin i; [exact a1 |].
  intro i; inv_fin i; [exact a2 |].
  intro i; inv_fin i.
Defined.

Definition b_1 (b : BExp L) : forall i : fin 1, support IMP_term_algebra (const is_B i).
Proof.
  intro i; inv_fin i; [exact b |].
  intro i; inv_fin i.
Defined.

Definition b_2 (b1 b2 : BExp L) : forall i : fin 2, support IMP_term_algebra (const is_B i).
Proof.
  intro i; inv_fin i; [exact b1 |].
  intro i; inv_fin i; [exact b2 |].
  intro i; inv_fin i.
Defined.

Definition c_2 (c1 c2 : Cmd L) : forall i : fin 2, support IMP_term_algebra (const is_C i).
Proof.
  intro i; inv_fin i; [exact c1 |].
  intro i; inv_fin i; [exact c2 |].
  intro i; inv_fin i.
Defined.

Definition term_support_star_if (b : BExp L) (c1 c2 : Cmd L) :
    support_star IMP_term_algebra (projT2 (@arity IMP_sign is_if)).
Proof.
  intro i; inv_fin i; [exact b |].
  intro i; inv_fin i; [exact c1 |].
  intro i; inv_fin i; [exact c2 |].
  intro i; inv_fin i.
Defined.

Definition term_support_star_while (b : BExp L) (c : Cmd L) :
    support_star IMP_term_algebra (projT2 (@arity IMP_sign is_while)).
Proof.
  intro i; inv_fin i; [exact b |].
  intro i; inv_fin i; [exact c |].
  intro i; inv_fin i.
Defined.

Lemma IMP_term_interp_a_unique:
    forall (A : algebra IMP_sign),
    forall (h : algebra_fn IMP_term_algebra A), AlgebraMorphism h ->
    IMP_term_interp_a A = h is_A.
Proof.
  intros * Hh.
  extensionality a; cbn in a.
  induction a; cbn.
  - specialize (Hh (is_int z) zero_dep_fn); cbn in Hh; rewrite Hh.
    by f_equal; extensionality i; inv_fin i.
  - specialize (Hh (is_var l) zero_dep_fn); cbn in Hh; rewrite Hh.
    by f_equal; extensionality i; inv_fin i.
  - specialize (Hh is_plus (a_2 a1 a2)); cbn in Hh; rewrite Hh.
    f_equal; extensionality i; inv_fin i; [done |].
    intro i; inv_fin i; [done |].
    by intro i; inv_fin i.
  - specialize (Hh is_minus (a_2 a1 a2)); cbn in Hh; rewrite Hh.
    f_equal; extensionality i; inv_fin i; [done |].
    intro i; inv_fin i; [done |].
    by intro i; inv_fin i.
  - specialize (Hh is_mul (a_2 a1 a2)); cbn in Hh; rewrite Hh.
    f_equal; extensionality i; inv_fin i; [done |].
    intro i; inv_fin i; [done |].
    by intro i; inv_fin i.
Qed.

Lemma IMP_term_interp_b_unique:
    forall (A : algebra IMP_sign),
    forall (h : algebra_fn IMP_term_algebra A), AlgebraMorphism h ->
    IMP_term_interp_b A = h is_B.
Proof.
  intros * Hh.
  extensionality b; cbn in b.
  induction b; cbn.
  - destruct b; cbn.
    + specialize (Hh is_true zero_dep_fn); cbn in Hh; rewrite Hh.
      by f_equal; extensionality i; inv_fin i.
    + specialize (Hh is_false zero_dep_fn); cbn in Hh; rewrite Hh.
      by f_equal; extensionality i; inv_fin i.
  - pose (Hrew := Hh is_eq (a_2 a a0)); cbn in Hrew; rewrite Hrew.
    f_equal; extensionality i;
      inv_fin i; [by erewrite IMP_term_interp_a_unique |].
    intro i; inv_fin i; [by erewrite IMP_term_interp_a_unique |].
    by intro i; inv_fin i.
  - pose (Hrew := Hh is_le (a_2 a a0)); cbn in Hrew; rewrite Hrew.
    f_equal; extensionality i;
      inv_fin i; [by erewrite IMP_term_interp_a_unique |].
    intro i; inv_fin i; [by erewrite IMP_term_interp_a_unique |].
    by intro i; inv_fin i.
  - specialize (Hh is_not (b_1 b)); cbn in Hh; rewrite Hh.
    f_equal; extensionality i; inv_fin i; [done |].
    by intro i; inv_fin i.
  - specialize (Hh is_and (b_2 b1 b2)); cbn in Hh; rewrite Hh.
    f_equal; extensionality i; inv_fin i; [done |].
    intro i; inv_fin i; [done |].
    by intro i; inv_fin i.
  - specialize (Hh is_or (b_2 b1 b2)); cbn in Hh; rewrite Hh.
    f_equal; extensionality i; inv_fin i; [done |].
    intro i; inv_fin i; [done |].
    by intro i; inv_fin i.
Qed.

Lemma IMP_term_interp_c_unique:
    forall (A : algebra IMP_sign),
    forall (h : algebra_fn IMP_term_algebra A), AlgebraMorphism h ->
    IMP_term_interp_c A = h is_C.
Proof.
  intros * Hh.
  extensionality c; cbn in c.
  induction c; cbn.
  - specialize (Hh is_skip zero_dep_fn); cbn in Hh; rewrite Hh.
    by f_equal; extensionality i; inv_fin i.
  - pose (Hrew := Hh (is_asgn l) (a_1 a)); cbn in Hrew; rewrite Hrew.
    f_equal; extensionality i;
      inv_fin i; [by erewrite IMP_term_interp_a_unique |].
    by intro i; inv_fin i.
  - specialize (Hh is_seq (c_2 c1 c2)); cbn in Hh; rewrite Hh.
    f_equal; extensionality i; inv_fin i; [done |].
    intro i; inv_fin i; [done |].
    by intro i; inv_fin i.
  - pose (Hrew := Hh is_if (term_support_star_if b c1 c2)); cbn in Hrew; rewrite Hrew.
    f_equal; extensionality i;
      inv_fin i; [by erewrite IMP_term_interp_b_unique |].
    intro i; inv_fin i; [done |].
    intro i; inv_fin i; [done |].
    by intro i; inv_fin i.
  - pose (Hrew := Hh is_while (term_support_star_while b c)); cbn in Hrew; rewrite Hrew.
    f_equal; extensionality i;
      inv_fin i; [by erewrite IMP_term_interp_b_unique |].
    intro i; inv_fin i; [done |].
    by intro i; inv_fin i.
Qed.

#[export] Instance IMP_term_algebra_initial : Initial IMP_term_algebra.
Proof.
  intro A.
  exists (IMP_term_interp A); split; [by typeclasses eauto |].
  intros h Hh. extensionality s.
  destruct s.
  - by apply IMP_term_interp_a_unique.
  - by apply IMP_term_interp_b_unique.
  - by apply IMP_term_interp_c_unique.
Qed.

Definition IMP_denot_support (s : sort IMP_sign) : Type :=
match s with
| is_A => State L -> Z
| is_B => State L -> bool
| is_C => Ensemble (State L * State L)
end.

Definition IMP_denot_op_interp (sigma : symbols IMP_sign)
    (tuple : support_star_helper IMP_denot_support (projT2 (arity sigma))) :
    IMP_denot_support (result_sort sigma) :=
match sigma as i
    return
        (support_star_helper IMP_denot_support (projT2 (@arity IMP_sign i)) ->
        IMP_denot_support (@result_sort IMP_sign i))
with
| is_int z => fun _ => const z
| is_var n => fun _ sigma => sigma n
| is_plus => fun tuple sigma => (tuple 0%fin sigma + tuple 1%fin sigma)%Z
| is_minus => fun tuple sigma => (tuple 0%fin sigma - tuple 1%fin sigma)%Z
| is_mul => fun tuple sigma => (tuple 0%fin sigma * tuple 1%fin sigma)%Z
| is_eq => fun tuple sigma => bool_decide (tuple 0%fin sigma = tuple 1%fin sigma)%Z
| is_le => fun tuple sigma => bool_decide (tuple 0%fin sigma <= tuple 1%fin sigma)%Z
| is_true => fun _ => const true
| is_false => fun _ => const false
| is_not => fun tuple sigma => negb (tuple 0%fin sigma)
| is_and => fun tuple sigma => andb (tuple 0%fin sigma) (tuple 1%fin sigma)
| is_or => fun tuple sigma => orb (tuple 0%fin sigma) (tuple 1%fin sigma)
| is_skip => fun _ => delta
| is_asgn n => fun tuple => denot_asgn n (tuple 0%fin)
| is_seq => fun tuple => fwd_relation_composition (tuple 0%fin) (tuple 1%fin)
| is_if => fun tuple => relation_selector (tuple 0%fin) (tuple 1%fin) (tuple 2%fin)
| is_while => fun tuple => lfp (while_step (tuple 0%fin) (tuple 1%fin))
end
  tuple.

Definition IMP_denot_algebra : algebra IMP_sign :=
{|
    support := IMP_denot_support;
    op_interp := IMP_denot_op_interp;
|}.

Lemma IMP_denot_algebra_a: IMP_term_interp_a IMP_denot_algebra = denota.
Proof.
  extensionality a; induction a.
  - done.
  - done.
  - extensionality sigma; cbn.
    by rewrite IHa1, IHa2.
  - extensionality sigma; cbn.
    by rewrite IHa1, IHa2.
  - extensionality sigma; cbn.
    by rewrite IHa1, IHa2.
Qed.

Lemma IMP_denot_algebra_b : IMP_term_interp_b IMP_denot_algebra = denotb.
Proof.
  extensionality b; induction b.
  - by destruct b.
  - by extensionality sigma; cbn; rewrite !IMP_denot_algebra_a.
  - by extensionality sigma; cbn; rewrite !IMP_denot_algebra_a.
  - extensionality sigma; cbn.
    by rewrite IHb.
  - extensionality sigma; cbn.
    by rewrite IHb1, IHb2.
  - extensionality sigma; cbn.
    by rewrite IHb1, IHb2.
Qed.

Lemma IMP_denot_algebra_c : IMP_term_interp_c IMP_denot_algebra = denotc.
Proof.
  extensionality c; induction c.
  - done.
  - by extensionality sigma; cbn; rewrite !IMP_denot_algebra_a.
  - extensionality sigma; cbn.
    by rewrite IHc1, IHc2.
  - extensionality sigma; cbn.
    by rewrite IMP_denot_algebra_b, IHc1, IHc2.
  - extensionality sigma; cbn.
    by rewrite IMP_denot_algebra_b, IHc.
Qed.

End sec_IMP_algebra.