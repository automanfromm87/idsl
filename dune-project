(lang dune 3.20)

(using menhir 3.0)

(name iDSL)

(generate_opam_files true)

(source
 (github automanfromm87/idsl))

(license MIT)

(package
 (name iDSL)
 (synopsis "Small rules DSL with type inference and explainable evaluation")
 (description
  "iDSL is a tiny rules language with raw and derived schema fields, named
   instances, and a typed rule-firing model. Compiles to a CLI, a full
   LSP 3.17 server, and a browser playground via js_of_ocaml.")
 (depends
  ocaml
  dune
  menhir)
 (tags
  (dsl parser language-server)))
