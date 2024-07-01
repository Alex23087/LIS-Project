FROM ocaml/opam:opensuse-ocaml-5.2
WORKDIR /home/opam/Failure
COPY . .

RUN opam init --reinit -ni
RUN opam update
RUN opam install dune ppx_deriving odoc ppx_inline_test menhirLib sexplib menhir
RUN opam exec -- make build

CMD ["bash"]
