# Dialectica interpretation into System T

A syntactic formalization in Rocq of Gödel's Dialectica interpretation of
Heyting arithmetic into Gödel's System T.

HA formulas are represented with intrinsically typed, de Bruijn-indexed
System T terms. A proof `d : proof Γ A` is translated to a System T witness
`wit d : tm Γ (W A)`. The resulting program can then be normalized with the
axiom-free normalization-by-evaluation development in the
[`nbe-system-t`](https://github.com/clayrat/nbe-system-t) submodule:

```coq
Definition realizer {Γ} {A : prp Γ} (d : proof Γ A) : nf Γ (W A) :=
  norm (wit d).
```

The translation and normal-form extraction pipeline are implemented. The
general Dialectica soundness theorem,

```coq
forall Γ (A : prp Γ) (d : proof Γ A), valid A (wit d)
```

is the next major milestone.

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
for f in Terms Eval HA Dialectica Realizer; do
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
| `nbe-system-t/` | Git submodule providing the shared System T syntax, OPEs, substitution, normal forms, NbE, and its metatheory |
| `theories/Terms.v` | Generic System T utilities, boolean programs, defaults, and natural-number equality |
| `theories/Eval.v` | Set-theoretic evaluator for System T |
| `theories/HA.v` | HA formulas, renaming/substitution, proof calculus, and derived rules |
| `theories/Dialectica.v` | Witness/counter translation, internal matrix, proof extraction, validity, and examples |
| `theories/Realizer.v` | Composition of Dialectica extraction with NbE normalization |
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
- the induction realizer's backward counterexample search computes.

See `PROGRESS.md` for the soundness plan and the relationship to the older
reference developments.
