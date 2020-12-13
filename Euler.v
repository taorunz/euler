Require Import Utf8 Arith.
Import List List.ListNotations.
Require Import Psatz Misc Primes Totient Primisc.

Definition prod (l : list nat) := fold_left Nat.mul l 1.
Arguments prod l /.

Definition pow_in_n n p := count_occ Nat.eq_dec (prime_decomp n) p.

Lemma prime_divisors_distinct : ∀ n, NoDup (prime_divisors n).
Admitted.

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

Variable pairwise_coprime : list nat -> Prop.

Theorem φ_prod_pairwise_coprime : 
    ∀ (l : list nat) (Hpc : pairwise_coprime l),
        φ (prod l) = prod (map φ l).
Proof.
    intros. induction l.
    - simpl. admit.
    - simpl in *. repeat rewrite Nat.add_0_r. 
      repeat rewrite fold_left_mul_from_1.
      apply IHl. 
