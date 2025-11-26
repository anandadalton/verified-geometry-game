(lang dune 3.20)
(using coq 0.8)

(name verified-geometry-game)
(package
 (name verified-geometry-game)
 (synopsis "Formal verification of Finite Affine Geometry (AG(4,3))")
 (depends
  (dune (>= 3.20))
  (coq (>= 9.1))
  (coq-stdlib (>= 9.1))
  (js_of_ocaml (>= 5.0))
  (js_of_ocaml-ppx (>= 5.0))
  (brr (>= 0.0.7))))
