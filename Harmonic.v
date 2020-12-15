(* Bound for Harmonic Series *)

Require Import Utf8 Arith.
Import List List.ListNotations.
Require Import Psatz Misc Prod.
Require Import Reals.

Local Open Scope R_scope.
Local Coercion INR : nat >-> R.

Theorem harmonic_upper_bound :
    ∀ (n : nat), fold_left Rplus (map (λ (x : nat), 1 / x) (seq 1 n)) 0 <= 2 * Nat.log2 n.
Admitted.

Local Close Scope R_scope.