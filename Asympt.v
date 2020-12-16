(* Asymptotoc bound for φ *)

Require Import Utf8 Arith.
Import List List.ListNotations.
Require Import Reals.

Require Import Psatz Misc Primes Totient Primisc Prod Harmonic.
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

Local Open Scope R_scope.
Local Coercion INR : nat >-> R.

Definition Rprod (l : list R) := fold_left Rmult l 1.
Arguments Rprod l /.

Definition Rsum (l : list R) := fold_left Rplus l 0.
Arguments Rsum l /.

Lemma fold_left_Rmult_from_1 :
    ∀ a l, fold_left Rmult l a = a * fold_left Rmult l 1.
Proof.
    intros. revert a. induction l.
    - intros. simpl. ring.
    - intros. simpl. rewrite IHl.
      rewrite IHl with (1 * a). ring.
Qed.

Lemma fold_left_Rmult_from_a :
    ∀ a b l, fold_left Rmult l (a * b) = b * fold_left Rmult l a.
Proof.
    intros. revert a. induction l.
    - intros. simpl. ring.
    - intros. simpl. 
      replace (a0 * b * a) with (a0 * a * b) by lra.
      rewrite IHl. ring.
Qed.

Lemma fold_left_Rplus_from_0 :
    ∀ a l, fold_left Rplus l a = a + fold_left Rplus l 0.
Proof.
    intros. revert a. induction l.
    - intros. simpl. ring.
    - intros. simpl. rewrite IHl.
      rewrite IHl with (0 + a). ring.
Qed.

Lemma fold_left_Rplus_from_a :
    ∀ a b l, fold_left Rplus l (a + b) = b + fold_left Rplus l a.
Proof.
    intros. revert a. induction l.
    - intros. simpl. ring.
    - intros. simpl.
      replace (a0 + b + a) with (a0 + a + b) by lra.
      rewrite IHl. reflexivity.
Qed.

Lemma fold_left_Rplus_gt_0 :
    ∀ {T} (l : list T) (g : T → R) (a : R),
        (a >= 0) → (l ≠ []) → (∀ x, x ∈ l → g x > 0) →
        fold_left Rplus (map g l) a > 0.
Proof.
    intros. destruct l.
    - contradict H0. reflexivity.
    - simpl. clear H0. revert H1. revert l.
      induction l.
      + simpl. intros. specialize H1 with t.
        assert (g t > 0) by auto. lra.
      + intros. simpl.
        rewrite fold_left_Rplus_from_a with (a + g t) _ _.
        assert (∀ x : T, x ∈ t :: l → g x > 0).
        {
            intros. apply H1. simpl. destruct H0; auto.
        }
        apply IHl in H0.
        assert (g a0 > 0).
        {
            apply H1. simpl. auto.
        }
        lra.
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

Lemma ln_Rprod_Rsum :
    ∀ l, (l ≠ []) → (∀ x, x ∈ l → 0 < x) → ln (Rprod l) = Rsum (map ln l).
Proof.
    intros. destruct l.
    - simpl. apply ln_1.
    - simpl. clear H. revert H0. revert l.
      induction l.
      + intros. simpl. rewrite Rmult_1_l. rewrite Rplus_0_l. reflexivity.
      + intros. simpl.
        rewrite Rmult_1_l, Rplus_0_l in *.
        rewrite fold_left_Rplus_from_a.
        rewrite fold_left_Rmult_from_a.
        rewrite ln_mult. rewrite IHl. reflexivity.
        intros. apply H0. destruct H. now left.
        right. now right.
        apply H0. right. left. reflexivity.
        apply Rgt_lt.
        replace l with (map id l).
        apply fold_left_Rmult_gt_0.
        apply Rlt_gt. apply H0. left. reflexivity.
        intros. unfold id. apply Rlt_gt. apply H0. right.
        right. assumption.
        clear. induction l. reflexivity. simpl. rewrite IHl. reflexivity.
Qed.

Lemma Rsum_map_le :
    ∀ l f g (Hle : ∀ x : nat, x ∈ l → f x <= g x),
        Rsum (map f l) <= Rsum (map g l).
Proof.
    intros. induction l.
    - simpl. lra.
    - simpl in *. repeat rewrite Rplus_0_l.
      rewrite fold_left_Rplus_from_0.
      rewrite fold_left_Rplus_from_0 with (g a) _.
      assert (f a <= g a).
      { apply Hle. now left. }
      assert (fold_left Rplus (map f l) 0 <= fold_left Rplus (map g l) 0).
      { apply IHl. intros. apply Hle. now right. }
      lra.
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

Lemma Rsum_increasing_f :
    ∀ (l1 l2 : list nat) (f : nat → R),
        (∀ i j, (i ∈ l1 ∨ i ∈ l2) → (j ∈ l1 ∨ j ∈ l2) → i ≤ j → f i <= f j) →
        (entrywise_le l1 l2) → Rsum (map f l1) <= Rsum (map f l2).
Proof.
    intros. induction H0.
    - lra.
    - simpl in *. repeat rewrite Rplus_0_l.
      rewrite fold_left_Rplus_from_0.
      rewrite fold_left_Rplus_from_0 with (f x2) _.
      apply H in Hlex; auto.
      assert (fold_left Rplus (map f l1) 0 <= fold_left Rplus (map f l2) 0).
      {
          apply IHentrywise_le. intros.
          apply H; auto. destruct H1; auto. destruct H2; auto.
      }
      lra.
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
    rewrite ln_Rprod_Rsum.
    rewrite map_map.
    eapply Rge_trans with (exp (Rsum (map (λ x : nat, - 2 / x) (prime_divisors n)))).
    apply Rle_ge. apply Raux.exp_le. apply Rsum_map_le.
    intros. replace ((x - 1) / x) with (1 - / x).
    replace (-2 / x) with (- 2 * (/ x)) by lra.
    apply Rge_le. apply ln_1_minus_x_ge_minus_2x.
    cut (2 <= x). intros. interval.
    replace 2 with (INR (2%nat)) by reflexivity.
    apply le_INR. apply prime_ge_2. eapply in_prime_decomp_is_prime.
    apply prime_divisors_decomp. apply H0. field. 
    apply prime_divisors_decomp in H0.
    apply in_prime_decomp_is_prime in H0. apply prime_ge_2 in H0.
    apply le_INR in H0. simpl in H0. lra.
    rewrite <- exp_ln. apply Rle_ge. apply Raux.exp_le.
    apply Rge_le. eapply Rge_trans. apply Rle_ge. eapply Rsum_increasing_f.
    2:{ apply seq_entrywise_le_prime_divisors. }
    intros. apply le_INR in H2. apply Rminus_le.
    unfold Rdiv, Rminus. rewrite Ropp_mult_distr_r.
    rewrite <- Rmult_plus_distr_l. apply Stdlib.Rmult_le_neg_pos; try lra.
    replace (/ i + - / j) with (/ i - / j) by reflexivity. 
    apply Rge_le. apply Rge_minus. apply Rle_ge. apply Raux.Rinv_le; auto.
    admit. (* 0 < i *)
    
    admit.
    (* side conditions *)
    - admit.
    - unfold not. intros. apply map_eq_nil in H0.
      apply prime_divisors_nil_iff in H0. admit.
    - admit.
    - apply Rgt_lt. apply fold_left_Rmult_gt_0.
      lra. intros. rewrite prime_divisors_decomp in H0.
      apply in_prime_decomp_is_prime in H0. apply prime_ge_2 in H0.
      apply le_INR in H0. simpl in *. apply Rdiv_lt_0_compat; lra.
    - intros. rewrite mult_INR. repeat rewrite pow_INR.
      rewrite minus_INR. simpl. 
      replace (pow_in_n n a) with (pow_in_n n a - 1 + 1)%nat at 2.
      rewrite Rdef_pow_add. rewrite pow_1. field.
      assert (INR a ≠ 0).
      {
        apply prime_divisors_decomp in H0.
        apply in_prime_decomp_is_prime in H0. apply prime_ge_2 in H0.
        apply le_INR in H0. simpl in H0. lra.
      }
      split. auto. 
      apply pow_nonzero. auto.
      specialize in_prime_divisors_power_ge_1 with n a as H1.
      apply H1 in H0. lia.
      apply prime_divisors_decomp in H0.
      apply in_prime_decomp_is_prime in H0. apply prime_ge_2 in H0. lia.
    - intros. assert (INR x ≠ 0).
      {
        apply prime_divisors_decomp in H0.
        apply in_prime_decomp_is_prime in H0. apply prime_ge_2 in H0.
        apply le_INR in H0. simpl in H0. lra.
      }
      rewrite pow_INR.
      now apply pow_nonzero.
    - admit.
    - admit.
    - admit. 
Admitted.

Local Close Scope R_scope.