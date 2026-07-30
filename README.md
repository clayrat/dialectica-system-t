# Dialectica interpretation into System T

A syntactic formalization in Rocq of Gödel's Dialectica interpretation of
Heyting arithmetic, extended with quantifier-free Markov's principle and
universal-premise Independence of Premise, into Gödel's System T.

Arithmetic formulas are represented with intrinsically typed, de
Bruijn-indexed System T terms. A derivation `d : proof Γ A` in the extended
calculus is translated to a System T witness `wit d : tm Γ (W A)`. The
ordinary HA derivations form its intuitionistic fragment. The resulting
program can then be normalized with the axiom-free
normalization-by-evaluation development in the
[`nbe-system-t`](https://github.com/clayrat/nbe-system-t) submodule:

```coq
Definition realizer {Γ} {A : prp Γ} (d : proof Γ A) : nf Γ (W A) :=
  norm (wit d).
```

The translation, soundness proof, and normal-form extraction pipeline are
implemented. In particular, the development proves

```coq
forall Γ (A : prp Γ) (d : proof Γ A), valid A (wit d)
```

and transfers validity to the normalized realizer `nf_emb (realizer d)`.
For closed formulas it also proves that the internal Dialectica matrix
normalizes to `true` against every closed syntactic counter.

## Requirements

- Git with submodule support
- Rocq 9.1

No additional Rocq packages are required.

## Clone and build

Clone the repository together with its submodule:

```sh
git clone --recurse-submodules <repository-url>
cd dialectica-system-t
```

For an existing checkout, initialize the dependency with:

```sh
git submodule update --init --recursive
```

Build the NbE development first:

```sh
cd nbe-system-t
~/.opam/rocq-9.1/bin/rocq makefile -f _CoqProject -o Makefile
PATH=~/.opam/rocq-9.1/bin:$PATH make
cd ..
```

Then compile this development in dependency order:

```sh
for f in Terms Semantics HA Dialectica Validity Realizer Examples; do
  ~/.opam/rocq-9.1/bin/rocq compile \
    -Q nbe-system-t/theories NbE \
    -Q theories SystemT \
    theories/$f.v
done
```

The `rocq makefile` bootstrap is needed once per fresh submodule checkout.
If Rocq 9.1 is already on `PATH`, the full executable path can be replaced
with `rocq`, and the explicit `PATH` assignment can be omitted.

## Repository layout

| Path | Contents |
| --- | --- |
| `nbe-system-t/` | Git submodule providing System T syntax, OPEs, substitution, normal forms, NbE, canonicity, and the standard set model with its PER metatheory |
| `theories/Terms.v` | Project System T utilities: notations, boolean connectives, addition, casts, and specialized substitutions |
| `theories/Semantics.v` | Dialectica-specific set-model facts for casts and project-specific substitutions |
| `theories/HA.v` | HA formulas, renaming/substitution, proof calculus, and derived rules |
| `theories/Dialectica.v` | Witness/counter translation, internal matrix program, and proof extraction |
| `theories/Validity.v` | Denotational matrix, validity predicate, and axiom-free Dialectica soundness proof |
| `theories/Realizer.v` | NbE normalization, validity transfer, and syntactic soundness |
| `theories/Examples.v` | Example derivations and their evaluation, normalization, validity, and matrix checks |
| `theories_old/` | Earlier semantic Rocq developments used as proof references |
| `src_old/` | Earlier Agda and game-semantics experiments |
| `PROGRESS.md` | Detailed design decisions, milestone status, and future work |

The shared syntax is imported as `NbE.Syntax`; this repository deliberately
does not define a second `SystemT.Syntax` module.

## Checked examples

The development includes executable examples showing that:

- a proof of `∃y. y = 2` extracts and normalizes to `(2, tt)`;
- a proof of `∀x. ∃y. y = S x` extracts and normalizes to
  `λx. (S x, tt)`;
- derivations through Markov's principle and Independence of Premise
  normalize to their concrete existential witnesses;
- the induction realizer's backward counterexample search computes;
- a proof of `∀x. x + 0 = x` uses induction and Leibniz substitution,
  exposes the residual induction skeleton in normal form, and has its
  arithmetic matrix checked at `x = 5`.

## OCaml extraction

`extraction/` (standalone, mirroring the `nbe-system-t` setup) extracts the
computational pipeline — `W`/`C`, `diaT`, `wit`, and `realizer` with the NbE
normalizer — to OCaml. Its dune driver pretty-prints the extracted realizers
of the showcase derivations and replays their closed Dialectica games with
the extracted normalizer, checking every matrix comes out `true`:

```
make -C extraction        # extract, build, run
```

`reference/dialectica_native.ml` is a hand-written, idiomatic (and
`Obj.magic`-free) OCaml rendering of the same pipeline, in the spirit of
`nbe-system-t`'s `reference/nbe_native.ml`; its driver asserts the same
normal forms the Rocq theorems prove (`ocaml reference/dialectica_native.ml`).

See `PROGRESS.md` for proof-design details, milestone history, and the
relationship to the older reference developments.
