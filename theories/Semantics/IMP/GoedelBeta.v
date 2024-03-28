From stdpp Require Import prelude finite.
From Coq Require Import IndefiniteDescription.

Definition beta_fn (a b i : nat) : nat := a `mod` (1 + (1 + i) * b).

Definition beta_p (m : nat) `(i : fin k) : nat := 1 + (1 + (fin_to_nat i)) * m.

Definition beta_m `(a : fin k -> nat) :=
  fact (max k (max_list (map a (enum (fin k))))).

Definition beta_pa `(a : fin k -> nat) (i : fin k) : nat :=
  beta_p (beta_m a) i.

Lemma fact_ge_n : forall (n : nat), n <= fact n.
Proof.
    induction n; cbn; [by lia |].
    by cut (0 < fact n); [nia | apply lt_O_fact].
Qed.

Lemma fact_ge_1 : forall (n : nat), 1 <= fact n.
Proof.
    induction n; cbn; [by lia |].
    by cut (0 < fact n); [nia | apply lt_O_fact].
Qed.

Lemma beta_lemma_a1 :
    forall (k : nat) (a : fin k -> nat),
    forall (i : fin k), a i < beta_pa a i.
Proof.
    intros.
    pose (max_a := max_list (map a (enum (fin k)))).
    pose (m := fact (max k max_a)).
    assert (Hai : a i <= k `max` max_a).
    {
      cut (a i <= max_a); [by lia |].
      apply max_list_elem_of_le, elem_of_list_fmap.
      by eexists; split; [| apply elem_of_enum].
    }
    unfold beta_p.
    remember (k `max` max_a) as maxx.
    subst m max_a; unfold beta_pa, beta_p, beta_m.
    rewrite <- Heqmaxx.
    specialize (fact_ge_n maxx).
    by lia.
Qed.

Lemma beta_lemma_a2:
    forall (k : nat) (a : fin k -> nat),
    forall (i j : fin k), j < i -> Nat.gcd (beta_pa a i) (beta_pa a j) = 1.
Proof.
    intros.
    pose (max_a := max_list (map a (enum (fin k)))).
    pose (m := fact (max k max_a)).
    unfold beta_p.
    remember (Nat.gcd _ _) as d.
    assert (Hdi : (d | beta_p m i)) by (subst; apply Nat.gcd_divide_l).
    assert (Hdj : (d | beta_p m j)) by (subst; apply Nat.gcd_divide_r).
    assert (Hdijm : (d | beta_p m i - beta_p m j)) by (apply Nat.divide_sub_r; done).
    replace (beta_p m i - beta_p m j) with ((i - j) * m) in Hdijm
      by (unfold beta_p; nia).
    apply Nat.divide_mul_l with (p := (i - j)) in Hdi as Hdi'.
    apply Nat.divide_mul_l with (p := (1 + i)) in Hdijm as Hdijm'.
    assert (Hdij : (d | beta_p m i * (i - j) - (i - j) * m * (1 + i)))
       by (apply Nat.divide_sub_r; done).
    replace (beta_p m i * (i - j) - (i - j) * m * (1 + i)) with (i - j) in Hdij
      by (unfold beta_p; nia).
    assert (i - j | m) as [mij ->].
    {
      subst m.
      cut (forall (m n : nat), 0 < m <= n -> (m | fact n)).
      {
        intro Hdiv; apply Hdiv; split; [by lia |].
        etransitivity; [| by apply Nat.le_max_l].
        etransitivity; [by apply Nat.le_sub_l |].
        by specialize (fin_to_nat_lt i); lia.
      }
      intros m n; revert m; induction n; [by lia |].
      intros m Hm. change (fact (S n)) with (S n * fact n).
      destruct (decide (m = S n));
        [by subst; apply Nat.divide_mul_l |].
      by apply Nat.divide_mul_r, IHn; lia.
    }
    apply Nat.divide_mul_l with (p := (1 + i) * mij) in Hdij as Hdij'.
    assert (Hdone : (d | beta_p (mij * (i - j)) i - (i - j) * ((1 + i) * mij)))
      by (apply Nat.divide_sub_r; done).
    replace ((beta_p (mij * (i - j)) i - (i - j) * ((1 + i) * mij))) with 1
      in Hdone by (unfold beta_p; nia).
    by apply Nat.divide_1_r.
Qed.

Definition prod_list_with {A} (f : A → nat) : list A → nat :=
    fix go l :=
    match l with
    | [] => 1
    | x :: l => f x * go l
    end.

Lemma prod_list_with_cons : forall `(f : A -> nat) (a : A) (l : list A),
    prod_list_with f (a :: l) = f a * prod_list_with f l.
Proof. done. Qed.

Lemma prod_list_with_not_zero : forall `(f : A -> nat) (l : list A),
    List.Forall (fun x => f x <> 0) l -> prod_list_with f l <> 0.
Proof. by intros *; induction 1; cbn; [| lia]. Qed.

Lemma prod_list_with_filter :
    forall `(f : A → nat) (P : A -> Prop) `{forall a, Decision (P a)} (l : list A),
    prod_list_with f l = prod_list_with f (filter P l) * prod_list_with f (filter (not ∘ P) l).
Proof.
    induction l; [done |].
    cbn.
    case_decide.
    - rewrite decide_False by (intro; done).
      by cbn; rewrite IHl, Nat.mul_assoc.
    - rewrite decide_True by done.
      cbn; rewrite IHl, !Nat.mul_assoc.
      by f_equal; apply Nat.mul_comm.
Qed.

Lemma sum_list_with_filter :
    forall `(f : A → nat) (P : A -> Prop) `{forall a, Decision (P a)} (l : list A),
    sum_list_with f l = sum_list_with f (filter P l) + sum_list_with f (filter (not ∘ P) l).
Proof.
    induction l; [done |].
    cbn.
    case_decide.
    - rewrite decide_False by (intro; done).
      by cbn; rewrite IHl, Nat.add_assoc.
    - rewrite decide_True by done.
      cbn; rewrite IHl, !Nat.add_assoc.
      by f_equal; apply Nat.add_comm.
Qed.

Lemma sum_list_with_mod : forall `(f : A -> nat) (l : list A) (n : nat),
    sum_list_with f l `mod` n = sum_list_with (fun a => f a `mod` n) l `mod` n.
Proof.
    intros; induction l; cbn; [done |].
    by rewrite Nat.Div0.add_mod, IHl, Nat.Div0.add_mod_idemp_r.
Qed.

Lemma sum_list_with_0 :  forall `(f : A -> nat) (l : list A),
    List.Forall (fun a => f a = 0) l ->
    sum_list_with f l = 0.
Proof. by intros *; induction 1; cbn; [| lia]. Qed.

Lemma gcd_1_mul : forall (n fl fa : nat), n <> 0 ->
    Nat.gcd fl n = 1 -> Nat.gcd fa n = 1 -> Nat.gcd (fa * fl) n = 1.
Proof.
    intros * Hn Hfl Hfa.
    destruct n; [done |].
    destruct n.
    - destruct (decide (fa * fl = 0)); [by rewrite e; apply Nat.gcd_0_l |].
      apply Nat.bezout_1_gcd; unfold Nat.Bezout.
      by exists 1, (fa * fl - 1); nia.
    - destruct (Nat.gcd_bezout_pos (S (S n)) fa) as (xa & ya & Hxya); [lia |].
      rewrite Nat.gcd_comm, Hfa in Hxya; clear Hfa.
      destruct (Nat.gcd_bezout_pos (S (S n)) fl) as (xl & yl & Hxyl); [lia |].
      rewrite Nat.gcd_comm, Hfl in Hxyl; clear Hfl.
      apply Nat.bezout_1_gcd; unfold Nat.Bezout.
      exists (ya * yl),  (xa * xl * S (S n) - xa - xl).
      replace ((xa * xl * S (S n) - xa - xl) * S (S n)) with
        ((xa * S (S n)) * (xl * S (S n)) - xa * S (S n) - xl * S (S n)) by nia.
      rewrite !Hxya, !Hxyl.
      assert (ya * fa <> 0) by (intro Hrew; rewrite Hrew in Hxya; lia).
      assert (yl * fl <> 0) by (intro Hrew; rewrite Hrew in Hxyl; lia).
      assert (ya * yl * (fa * fl) <> 0) by nia.
      replace ((1 + ya * fa) * (1 + yl * fl)) with (ya * yl * (fa * fl) + (1 + ya * fa) + yl * fl) by nia.
      by lia.
Qed.

Lemma prod_list_with_gcd :
    forall `(f : A -> nat) (l : list A) (n : nat), n <> 0 ->
    List.Forall (fun i => Nat.gcd (f i) n = 1) l ->
    Nat.gcd (prod_list_with f l) n = 1.
Proof.
    intros * Hn; induction l;
      [by intros _; apply Nat.bezout_1_gcd; exists 1, 0 |].
    rewrite Forall_cons; intros [Ha Hall].
    specialize (IHl Hall); clear Hall.
    rewrite prod_list_with_cons.
    by apply gcd_1_mul.
Qed.

Lemma prod_list_with_in : forall (A : Type) (x : A) (f : A → nat) (ls : list A),
    x ∈ ls -> (f x | prod_list_with f ls).
Proof.
    induction 1; [by cbn; rewrite Nat.mul_comm; eexists |].
    destruct IHelem_of_list as [a Ha].
    cbn; rewrite Ha.
    by exists (f y * a); nia.
Qed.

Definition beta_pa_product `(a : fin k -> nat) : nat :=
    prod_list_with (beta_pa a) (enum (fin k)).

Definition beta_c `(a : fin k -> nat) (i : fin k) : nat :=
    prod_list_with (beta_pa a) (filter (fun j => j <> i) (enum (fin k))).

Lemma filter_singleton : forall (A : Type) `{EqDecision A} (l : list A) (a : A),
  NoDup l -> a ∈ l -> filter (fun b => b = a) l = [a].
Proof.
    intros * Hnodup Ha.
    apply Permutation_singleton_r, NoDup_Permutation_bis.
    - by apply NoDup_ListNoDup, NoDup_filter.
    - cut ( length (filter (λ b : A, b = a) l)
            =
            if decide(a ∈ l) then 1 else 0);
        [by intros ->; rewrite decide_True |].
      revert Hnodup; clear; induction l; cbn;
        [by rewrite decide_False; [| inversion 1] |].
      rewrite NoDup_cons; intros [Ha0 Hnodup].
      destruct (decide (a0 = a)).
      + subst; rewrite decide_True by left.
        rewrite decide_False in IHl by done; cbn.
        by unfold filter in *; cbn in *; rewrite IHl.
      + unfold filter in *; cbn in *; rewrite IHl by done.
        case_decide.
        * by rewrite decide_True by (right; done).
        * by rewrite decide_False; [| inversion 1].
    - intros j. rewrite <- !elem_of_list_In, elem_of_list_singleton, elem_of_list_filter.
      by intros [-> _].
Qed.

Lemma beta_c_char : forall `(a : fin k -> nat) (i : fin k),
    beta_pa_product a = beta_c a i * beta_pa a i.
Proof.
    intros.
    unfold beta_pa_product.
    erewrite prod_list_with_filter with (P := fun j => j <> i).
    f_equal.
    erewrite list_filter_iff with (P2 := fun j => j = i), filter_singleton.
    - by cbn; lia.
    - by apply NoDup_enum.
    - by apply elem_of_enum.
    - intro; cbn; split; intro Hxi.
      + by destruct (decide (x = i)).
      + by destruct (decide (x <> i)).
Qed.

Lemma Zn_multiplicative_inverse :
    forall (m n : nat), m <> 0 -> 1 < n -> Nat.gcd m n = 1 ->
    exists! (d : nat), d < n /\ (d * m) `mod` n = 1.
Proof.
    intros * Hm Hn Hgcd.
    destruct (Nat.gcd_bezout_pos m n) as (a & b & Hab); [by lia |].
    rewrite Hgcd in Hab.
    assert (Hmod : (a `mod` n * m) `mod` n = 1).
    {
      rewrite Nat.Div0.mul_mod_idemp_l, Hab.
      rewrite Nat.Div0.mod_add.
      by apply Nat.mod_1_l; lia.
    }
    exists (a `mod` n); split.
    - split; [| done].
      by apply Nat.mod_bound_pos; lia.
    - intros a' [Ha' Hmod'].
      rewrite Nat.Div0.mod_eq in Hmod', Hmod at 1.
      destruct (decide (a' <= a `mod` n)).
      + assert (Hdiv: (n | a `mod` n - a')).
        {
          apply Nat.gauss with m; [| by rewrite Nat.gcd_comm].
          exists ((a `mod` n * m) `div` n - (a' * m) `div` n).
          by nia.
        }
        assert (a `mod` n - a' < n).
        {
          cut (a `mod` n < n); [by lia |].
          by apply Nat.mod_upper_bound; lia.
        }
        destruct (decide (a `mod` n - a' = 0)); [by lia |].
        apply Nat.divide_pos_le in Hdiv; by lia.
      + assert (Hdiv: (n | a' - a `mod` n)).
        {
          apply Nat.gauss with m; [| by rewrite Nat.gcd_comm].
          exists ((a' * m) `div` n - (a `mod` n * m) `div` n).
          by nia.
        }
        assert (a' - a `mod` n < n).
        {
          cut (a `mod` n < n); [by lia |].
          by apply Nat.mod_upper_bound; lia.
        }
        destruct (decide (a' - a `mod` n = 0)); [by lia |].
        apply Nat.divide_pos_le in Hdiv; by lia.
Qed.

Lemma beta_lemma_b :
    forall (k : nat) (a : fin k -> nat) (i : fin k),
    exists! (d : nat), d < beta_pa a i /\ (d * beta_c a i) `mod` beta_pa a i = 1.
Proof.
    intros.
    apply Zn_multiplicative_inverse.
    - apply prod_list_with_not_zero.
      apply Forall_forall; intros j _.
      by unfold beta_pa, beta_p; lia.
    - unfold beta_pa, beta_p, beta_m.
      by specialize (fact_ge_1 (k `max` max_list (map a (enum (fin k))))); nia.
    - apply prod_list_with_gcd.
      + by unfold beta_pa, beta_p; lia.
      + apply Forall_forall; intro j.
        rewrite elem_of_list_filter; intros [Hij _].
        destruct (decide (i < j)); [by apply beta_lemma_a2 |].
        rewrite Nat.gcd_comm; apply beta_lemma_a2.
        cut (fin_to_nat i <> fin_to_nat j); [by lia |].
        clear -Hij.
        contradict Hij.
        pose proof (Hi := fin_to_nat_lt i).
        rewrite <- nat_to_fin_to_nat with (H := Hi).
        revert Hi.
        rewrite Hij.
        intro Hj.
        by rewrite nat_to_fin_to_nat.
Qed.

Definition beta_lemma_b_choice `(a : fin k -> nat) (i : fin k) :
    {d : nat | d < beta_pa a i /\ (d * beta_c a i) `mod` beta_pa a i = 1}.
Proof.
    apply constructive_definite_description, beta_lemma_b.
Qed.

Definition beta_d `(a : fin k -> nat) (i : fin k) : nat :=
    proj1_sig (beta_lemma_b_choice a i).

Lemma beta_d_prop1 : forall (k : nat) (a : fin k -> nat) (i : fin k),
    beta_d a i < beta_pa a i.
Proof.
    intros. unfold beta_d.
    by destruct beta_lemma_b_choice as (? & ? & ?).
Qed.

Lemma beta_d_prop2 : forall (k : nat) (a : fin k -> nat) (i : fin k),
    (beta_c a i * beta_d a i) `mod` beta_pa a i = 1.
Proof.
    intros. rewrite Nat.mul_comm. unfold beta_d.
    by destruct beta_lemma_b_choice as (? & ? & ?).
Qed.

Definition beta_n `(a : fin k -> nat) :=
    sum_list_with (fun i => beta_c a i * beta_d a i * a i) (enum (fin k)).

Lemma beta_lemma_c : forall (k : nat) (a : fin k -> nat) (i : fin k),
    beta_n a `mod` beta_pa a i = a i.
Proof.
    intros.
    unfold beta_n.
    erewrite sum_list_with_filter with (P := fun j => j = i), filter_singleton;
      [| by apply NoDup_enum | by apply elem_of_enum].
    replace (sum_list_with (λ i0 : fin k, beta_c a i0 * beta_d a i0 * a i0) [i])
      with (beta_c a i * beta_d a i * a i)
      by (cbn; lia).
    rewrite Nat.Div0.add_mod.
    replace (sum_list_with _ _ `mod` beta_pa a i) with 0.
    - replace ((beta_c a i * beta_d a i * a i) `mod` beta_pa a i) with (a i).
      + replace (a i + 0) with (a i) by lia.
        by apply Nat.mod_small, beta_lemma_a1.
      + rewrite <- Nat.Div0.mul_mod_idemp_l, beta_d_prop2.
        replace (1 * a i) with (a i) by lia.
        by symmetry; apply Nat.mod_small, beta_lemma_a1.
    - rewrite sum_list_with_mod, sum_list_with_0, Nat.Div0.mod_0_l; [done |].
      apply Forall_forall; intro j.
      rewrite elem_of_list_filter; intros [Hj _]; cbn in Hj.
      rewrite <- Nat.mul_assoc, <- Nat.Div0.mul_mod_idemp_l.
      replace (beta_c a j `mod` beta_pa a i) with 0; [by apply Nat.Div0.mod_0_l |].
      symmetry; apply Nat.Lcm0.mod_divide.
      apply prod_list_with_in, elem_of_list_filter.
      by split; [| apply elem_of_enum].
Qed.

Lemma beta_lemma :
    forall (k : nat) (a : fin k -> nat),
    exists (n m : nat),
        forall (j : fin k),
        beta_fn n m j = a j.
Proof.
    intros.
    exists (beta_n a), (beta_m a).
    by apply beta_lemma_c.
Qed.
