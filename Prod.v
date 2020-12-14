(* Product formula of φ *)

Require Import Utf8 Arith.
Import List List.ListNotations.
Require Import Psatz Misc Primes Totient Primisc.

Definition prod (l : list nat) := fold_left Nat.mul l 1.
Arguments prod l /.

Definition pow_in_n n p := count_occ Nat.eq_dec (prime_decomp n) p.

Lemma in_prime_divisors_power_ge_1 :
    ∀ n p, p ∈ prime_divisors n → 1 ≤ pow_in_n n p.
Proof.
    intros. unfold pow_in_n.
    apply count_occ_In. 
    apply prime_divisors_decomp. assumption.
Qed.

Lemma prime_divisors_distinct : ∀ n, NoDup (prime_divisors n).
Proof.
    intros.
    unfold prime_divisors.
    apply NoDup_filter.
    apply seq_NoDup.
Qed.

Theorem prod_by_occ :
    forall (l1 l2 : list nat)
        (Hocc : forall x, x ∈ l1 -> x ∈ l2)
        (Hdis : NoDup l2),
    prod l1 = 
    prod (map (fun x => x ^ (count_occ Nat.eq_dec l1 x)) l2). 
Admitted.

Theorem prime_divisor_pow_prod :
    ∀ n, n ≠ 0 → prod (map (fun x => x ^ (pow_in_n n x)) (prime_divisors n)) = n.
Proof.
    intros. rewrite <- prime_decomp_prod; auto.
    unfold pow_in_n. symmetry. apply prod_by_occ.
    apply prime_divisors_decomp. apply prime_divisors_distinct.
Qed.

Inductive pairwise_coprime : list nat -> Prop :=
    | PCnil : pairwise_coprime nil
    | PCcons (x : nat) (l : list nat)
        (Hxlc : ∀ y, y ∈ l → Nat.gcd x y = 1)
        (Hlpc : pairwise_coprime l) : pairwise_coprime (x :: l).

Theorem φ_prod_pairwise_coprime : 
    ∀ (l : list nat) (Hpc : pairwise_coprime l),
        φ (prod l) = prod (map φ l).
Proof.
    intros. induction Hpc.
    - simpl. reflexivity. (* φ 1 = 1 *)
    - simpl in *. repeat rewrite Nat.add_0_r. 
      rewrite fold_left_mul_from_1.
      rewrite fold_left_mul_from_1 with (φ x) _.
      rewrite φ_multiplicative. rewrite IHHpc. reflexivity.
      clear - Hpc Hxlc.
      induction l.
      + simpl. apply Nat.gcd_1_r.
      + simpl. rewrite plus_0_r. replace a with (1 * a) by flia.
        rewrite <- List_fold_left_mul_assoc.
        rewrite Nat_gcd_1_mul_r. flia.
        inversion Hpc. apply IHl.
        --  intros. apply Hxlc. now right.
        --  assumption.
        --  apply Hxlc. now left.
Qed. 

Lemma prime_divisors_aux :
    ∀ n a, a ∈ prime_divisors n ->
        prime a ∧ pow_in_n n a > 0.
Proof.
    intros. split.
    apply in_prime_decomp_is_prime with n.
    apply prime_divisors_decomp. assumption.
    apply in_prime_divisors_power_ge_1 in H.
    flia H.
Qed.

Lemma diff_prime_power_coprime :
    ∀ x y px py,
        prime x → prime y → 1 ≤ px → 1 ≤ py → Nat.gcd (x ^ px) (y ^ py) = 1.
Admitted.

Lemma prime_power_pairwise_coprime :
    ∀ l (f : nat → nat) (HND : NoDup l) (Hprime : ∀ x, x ∈ l → prime x)
        (Hf : ∀ x, x ∈ l → 1 ≤ f x),
        pairwise_coprime (map (λ x, x ^ f x) l).
Proof.
    intros. induction l.
    - simpl. constructor.
    - simpl. constructor.
      + intros. rewrite in_map_iff in H.
        destruct H as (x & H1 & H2). subst.
        apply diff_prime_power_coprime.
        apply Hprime. now left.
        apply Hprime. now right.
        apply Hf. now left.
        apply Hf. now right.
      + apply IHl. inversion HND. assumption.
        intros. apply Hprime. now right.
        intros. apply Hf. now right.
Qed.

Theorem φ_prime_divisors_power :
    ∀ n, n ≠ 0 ->
        φ n = prod (map (fun x => x ^ (pow_in_n n x - 1) * (x - 1)) (prime_divisors n)).
Proof.
    intros.
    rewrite <- (prime_divisor_pow_prod n) at 1 by flia H.
    rewrite φ_prod_pairwise_coprime.
    rewrite map_map.
    rewrite map_ext_in with _ _ _ (λ x : nat, x ^ (pow_in_n n x - 1) * (x - 1)) _. reflexivity.
    - intros.
      apply prime_divisors_aux in H0 as (H0 & H1).
      assert (pow_in_n n a ≠ 0) by flia H1.
      rewrite prime_pow_φ by assumption.
      rewrite prime_φ by assumption. reflexivity.
    - apply prime_power_pairwise_coprime.
      apply prime_divisors_distinct.
      intros. apply prime_divisors_decomp in H0.
      apply in_prime_decomp_is_prime with n. assumption.
      apply in_prime_divisors_power_ge_1.
Qed.
      