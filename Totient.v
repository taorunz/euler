(* Correct Definition of φ *)

Require Import Utf8 Arith.
Import List List.ListNotations.
Require Import Misc Primes.
Require Import PTotient Primisc.


Definition coprimes n := filter (λ d, Nat.gcd n d =? 1) (seq 1 n).
Definition φ n := length (coprimes n).

Lemma coprimes_coprimes' :
    ∀ n, 2 ≤ n → coprimes n = coprimes' n.
Proof.
    intros. unfold coprimes, coprimes'.
    replace n with ((n - 1) + 1) at 1 by flia H.
    rewrite seq_app.
    replace (1 + (n - 1)) with n at 1 by flia H.
    rewrite filter_app. simpl.
    destruct (Nat.eqb_spec (Nat.gcd n n) 1).
    - rewrite Nat.gcd_diag in *. flia H e.
    - rewrite app_nil_r. reflexivity.
Qed.

Lemma φ_φ' :
    ∀ n, 2 ≤ n → φ n = φ' n.
Proof.
    intros. unfold φ, φ'.
    rewrite coprimes_coprimes' by flia H.
    reflexivity.
Qed.

Theorem prime_φ :
    ∀ p, prime p → φ p = p - 1.
Proof.
    intros.
    rewrite <- prime_φ' by assumption.
    apply φ_φ'. apply prime_ge_2. assumption.
Qed.

Theorem φ_multiplicative :
    ∀ m n, 
        Nat.gcd m n = 1 →
        φ (m * n) = φ m * φ n.
Proof.
    

