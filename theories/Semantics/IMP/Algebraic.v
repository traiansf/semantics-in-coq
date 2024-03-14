From stdpp Require Import prelude.
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

Inductive imp_sort : Type := is_A | is_B | is_C.

Inductive imp_symbols : Type :=
(* arithmetic exps *)
| is_int : Z -> imp_symbols
| is_var : nat -> imp_symbols
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
| is_asgn : nat -> imp_symbols
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

Definition zero_fn (a : fin 0) : imp_sort :=
    fin_0_inv _ a.

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
| is_A => AExp
| is_B => BExp
| is_C => Cmd
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

Fixpoint term_interp_a (a : AExp) : support A is_A :=
match a with
| AVal n => op_interp A (is_int n) (fin_0_inv _)
| Var x => op_interp A (is_var x) (fin_0_inv _)
| Plus a1 a2 =>
    op_interp A is_plus
        (fun i =>
            match i with
            | 0%fin => term_interp_a a1
            | _ => term_interp_a a2
            end)
| Minus a1 a2 =>
    op_interp A is_minus
        (fun i =>
            match i with
            | 0%fin => term_interp_a a1
            | _ => term_interp_a a2
            end)
| Mul a1 a2 =>
    op_interp A is_mul
        (fun i =>
            match i with
            | 0%fin => term_interp_a a1
            | _ => term_interp_a a2
            end)
end.

Fixpoint term_interp_b (b : BExp) : support A is_B :=
match b with
| BVal true => op_interp A is_true (fin_0_inv _)
| BVal false => op_interp A is_false (fin_0_inv _)
| AEq a1 a2 =>
    op_interp A is_eq
        (fun i =>
            match i with
            | 0%fin => term_interp_a a1
            | _ => term_interp_a a2
            end)
| ALe a1 a2 =>
    op_interp A is_le
        (fun i =>
            match i with
            | 0%fin => term_interp_a a1
            | _ => term_interp_a a2
            end)
| Not b => op_interp A is_not (const (term_interp_b b))
| And b1 b2 =>
    op_interp A is_and
        (fun i =>
            match i with
            | 0%fin => term_interp_b b1
            | _ => term_interp_b b2
            end)
| Or b1 b2 =>
    op_interp A is_or
        (fun i =>
            match i with
            | 0%fin => term_interp_b b1
            | _ => term_interp_b b2
            end)
end.

Definition term_interp_if
    (b : support A is_B) (c1 c2 : support A is_C) : support A is_C.
Proof.
    eapply (op_interp A is_if).
    intro i; cbn in *.
    destruct i as [| []] eqn: Hi.
    - exact b.
    - exact c1.
    - exact c2.
Defined.

Definition term_interp_while
    (b : support A is_B) (c : support A is_C) : support A is_C.
Proof.
    eapply (op_interp A is_while).
    intro i; cbn in *.
    destruct i.
    - exact b.
    - exact c.
Defined.

Fixpoint term_interp_c (c : Cmd) : support A is_C :=
match c with
| Skip => op_interp A is_skip (fin_0_inv _)
| Asgn x a => op_interp A (is_asgn x) (const (term_interp_a a))
| Seq c1 c2 =>
    op_interp A is_seq
        (fun i =>
            match i with
            | 0%fin => term_interp_c c1
            | _ => term_interp_c c2
            end)
| If b c1 c2 =>
    term_interp_if (term_interp_b b) (term_interp_c c1) (term_interp_c c2)
| While b c =>
    term_interp_while (term_interp_b b) (term_interp_c c)
end.

End sec_term_interp.

Definition IMP_denot_support (s : sort IMP_sign) : Type :=
match s with
| is_A => State -> Z
| is_B => State -> bool
| is_C => Ensemble (State * State)
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

End sec_IMP_algebra.