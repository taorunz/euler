Require Import Utf8 Arith.
Import List List.ListNotations.
Require Import Psatz Misc Primes Totient Primisc.

Definition prod (l : list nat) := fold_left Nat.mul l 1.
Arguments prod l /.

Definition pow_in_n n p := count_occ Nat.eq_dec (prime_decomp n) p.

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
    - simpl. admit. (* φ 1 = 1 *)
    - simpl in *. repeat rewrite Nat.add_0_r. 
      rewrite fold_left_mul_from_1.
      rewrite fold_left_mul_from_1 with (φ x) _.
      rewrite φ_multiplicative. rewrite IHHpc. reflexivity.
Admitted.

Lemma prime_divisors_aux :
    ∀ n a, a ∈ prime_divisors n ->
        prime a ∧ pow_in_n n a > 0.
Proof.
    intros. split.
    apply in_prime_decomp_is_prime with n.
    apply prime_divisors_decomp. assumption.
    unfold pow_in_n. apply count_occ_In. 
    apply prime_divisors_decomp. assumption.
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
    - admit.
Admitted.
      