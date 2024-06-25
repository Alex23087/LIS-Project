(lang dune 3.14)

(name failure_ssil_analyzer)

(generate_opam_files true)

(source
 (uri https://github.com/Alex23087/Failure-SSIL-Analyser))

(authors
  "Yuri Andriaccio"
  "Marco Antonio Corallo"
  "Andrea Simone Costa"
  "Elvis Rossi"
  "Alessandro Scala"
  "Samuele Bonini"
  "Andrea Castagna"
  "Fabio Federico"
  "Matteo Simone"
)

(using menhir 3.0)

(license GPL-3.0-or-later)

(package
 (name failure_ssil_analyzer)
 (depends ocaml dune)
)
