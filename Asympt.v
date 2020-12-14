(* Asymptotoc bound for φ *)

Require Import Utf8 Arith.
Import List List.ListNotations.
Require Import Psatz Misc Primes Totient Primisc Prod.
Require Import Reals.
Require Import Interval.Tactic.

(* Proof sketch:
φ n / n = prod[p | n] (1 - 1 / p)
= exp sum[p | n] ln (1 - 1 / p)
≥ exp sum[p | n] -2 (1/p)
≥ exp sum[i ∈ [log n]] -2 (1/i)
≥ exp -O(log log n)
= 1 / O(log n)
*)

Open Scope R_scope.
Coercion INR : nat >-> R.


Lemma ln_1_minus_x_ge_minus_2x :
    ∀ x : R, 0 <= x <= 1/2 → ln (1 - x) >= - 2 * x.
Proof.
    intros.
    apply Rminus_ge.
    interval with (i_autodiff x).
Qed.




