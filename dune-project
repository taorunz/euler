(lang dune 2.8)
(version 1.0.0)
(using coq 0.2)

(generate_opam_files true)

(package
 (name coq-euler)
 (synopsis "Asymptotic lower bound of the Euler Totient Function")
 (description "\| Coq proof for the asymptotic upper bound of the
              "\|  Euler Totient Function φ
 )
 (depends
   (coq-interval (>= 4.0.0))
   (coq (>= 8.10))))