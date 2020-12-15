(* Asymptotoc bound for φ *)

Require Import Utf8 Arith.
Import List List.ListNotations.
Require Import Psatz Misc Primes Totient Primisc Prod.
Require Import Reals.
Require Import Interval.Tactic.
Require Import Logic.FunctionalExtensionality.

(* Proof sketch:
φ n / n = prod[p | n] (1 - 1 / p)
= exp sum[p | n] ln (1 - 1 / p)
≥ exp sum[p | n] -2 (1/p)
≥ exp sum[i ∈ [Nat.log2 n]] -2 (1/i)
≥ exp -O(log log n)
= 1 / O(log n)
*)

Open Scope R_scope.
Coercion INR : nat >-> R.

Definition Rprod (l : list R) := fold_left Rmult l 1.
Arguments Rprod l /.

Lemma fold_left_Rmult_from_1 :
    ∀ a l, fold_left Rmult l a = a * fold_left Rmult l 1.
Proof.
    intros. revert a. induction l.
    - intros. simpl. ring.
    - intros. simpl. rewrite IHl.
      rewrite IHl with (1 * a). ring.
Qed.

Lemma Rmult_ne_0 :
    ∀ (a b : R) , a * b ≠ 0 ↔ (a ≠ 0 ∧ b ≠ 0).
Proof.
    intros. split; nra.
Qed.


Lemma fold_left_Rmult_ne_0 :
    ∀ {T} (l : list T) (g : T → R) (a : R),
        (a ≠ 0) → (∀ x, x ∈ l → g x ≠ 0) →
        fold_left Rmult (map g l) a ≠ 0.
Proof.
    induction l.
    - intros. simpl. assumption.
    -
      intros. simpl. rewrite fold_left_Rmult_from_1.
      specialize IHl with g 1. 
      assert (1 ≠ 0) by lra.
      apply IHl in H1.
      rewrite Rmult_ne_0. rewrite Rmult_ne_0.
      split. split. auto.
      apply H0. now left. apply H1.
      intros.
      apply H0. now right.
Qed.

Lemma fold_left_Rmult_ge_0 :
    ∀ {T} (l : list T) (g : T → R) (a : R),
        (a >= 0) → (∀ x, g x >= 0) →
        fold_left Rmult (map g l) a >= 0.
Proof.
    induction l.
    - intros. simpl. assumption.
    -
      intros. simpl. rewrite fold_left_Rmult_from_1.
      specialize IHl with g 1. 
      assert (1 >= 0) by lra.
      apply IHl in H1. apply Rle_ge.
      apply Stdlib.Rmult_le_pos_pos.
      apply Stdlib.Rmult_le_pos_pos. lra.
      specialize H0 with a. lra. lra. assumption.
Qed.

Lemma fold_left_Rmult_gt_0 :
    ∀ {T} (l : list T) (g : T → R) (a : R),
        (a > 0) → (∀ x, x ∈ l → g x > 0) →
        fold_left Rmult (map g l) a > 0.
Proof.
    induction l.
    - intros. simpl. assumption.
    -
      intros. simpl. rewrite fold_left_Rmult_from_1.
      specialize IHl with g 1. 
      assert (1 > 0) by lra.
      apply IHl in H1. apply Rlt_gt.
      apply Rmult_lt_0_compat.
      apply Rmult_lt_0_compat. lra.
      specialize H0 with a.
      assert (a ∈ a :: l) by now left. apply H0 in H2.
      lra. lra. intros. apply H0. now right.
Qed.

Theorem prod_INR_Rprod :
    ∀ (l : list nat), INR (prod l) = Rprod (map INR l).
Proof.
    intros. simpl.
    induction l.
    - reflexivity.
    - simpl. rewrite plus_0_r. rewrite Rmult_1_l.
      rewrite fold_left_mul_from_1.
      rewrite fold_left_Rmult_from_1.
      rewrite mult_INR. rewrite IHl. reflexivity.
Qed.

Theorem Rprod_div :
    ∀ {T} (f g : T → R) l (Hgne0 : ∀ x, x ∈ l → g x ≠ 0),
        Rprod (map f l) / Rprod (map g l) = Rprod (map (λ (x : T), (f x) / (g x)) l).
Proof.
    intros. induction l.
    - simpl. field.
    - simpl in *. 
      rewrite fold_left_Rmult_from_1.
      rewrite fold_left_Rmult_from_1 with (1 * g a) _.
      rewrite fold_left_Rmult_from_1 with (1 * (f a / g a)) _.
      rewrite <- IHl. field. split.
      apply fold_left_Rmult_ne_0. auto.
      intros. apply Hgne0. now right.
      apply Hgne0. now left.
      intros. apply Hgne0. auto. 
Qed.

Lemma ln_1_minus_x_ge_minus_2x :
    ∀ x : R, 0 <= x <= 1/2 → ln (1 - x) >= - 2 * x.
Proof.
    intros.
    apply Rminus_ge.
    interval with (i_autodiff x).
Qed.

Lemma len_prime_divisors_le_log2 :
    ∀ n, length (prime_divisors n) ≤ Nat.log2 n.
Admitted.

Inductive entrywise_le : list nat → list nat → Prop :=
    | entrywise_le_nil : entrywise_le [] []
    | entrywise_le_cons x1 l1 x2 l2 (Hlex : x1 ≤ x2) (Hlel : entrywise_le l1 l2): entrywise_le (x1 :: l1) (x2 :: l2).

Lemma seq_entrywise_le_prime_divisors :
    ∀ n, entrywise_le (seq 1 (length (prime_divisors n))) (prime_divisors n).
Admitted.

Lemma  Rprod_increasing_f :
    ∀ (l1 l2 : list nat) (f : nat → R),
        (∀ i j, i ≤ j → f i <= f j) →
        (∀ i, f i >= 0) →
        (entrywise_le l1 l2) → Rprod (map f l1) <= Rprod (map f l2).
Proof.
    intros. induction H1.
    - lra.
    - simpl in *. repeat rewrite Rmult_1_l.
      rewrite fold_left_Rmult_from_1.
      rewrite fold_left_Rmult_from_1 with (f x2) _.
      specialize (fold_left_Rmult_ge_0 l1 f 1) as Hl1.
      specialize (fold_left_Rmult_ge_0 l2 f 1) as Hl2.
      assert (1 >= 0) by lra.
      apply Hl1 in H2 as Hl11.
      apply Hl2 in H2 as Hl22.
      specialize H with x1 x2. apply H in Hlex.
      specialize H0 with x1 as Hx1.
      specialize H0 with x2 as Hx2. nra.
      apply H0. apply H0.
Qed.

Theorem φ_lower_bound :
    ∃ (N0 : nat) (c : R),
        (∀ n, N0 ≤ n → φ n / n >= c / Nat.log2 n) ∧ c > 0.
Proof.
    esplit. esplit. split.
    intros. 
    rewrite <- (prime_divisor_pow_prod n) at 2.
    rewrite φ_prime_divisors_power.
    repeat rewrite prod_INR_Rprod.
    repeat rewrite map_map.
    rewrite Rprod_div. 
    rewrite map_ext_in with _ _ _ (λ x : nat, (x - 1) / x) _.
    rewrite <- exp_ln with (Rprod _).
    - admit.
    - apply Rgt_lt. apply fold_left_Rmult_gt_0.
      lra. intros. rewrite prime_divisors_decomp in H0.
      apply in_prime_decomp_is_prime in H0. apply prime_ge_2 in H0.
      apply le_INR in H0. simpl in *. apply Rdiv_lt_0_compat; lra.
    - (* need x >= 1 *) admit.
    - (* need x >= 1 *) admit.
    - admit.
    - admit.
    - admit. 
Admitted.
