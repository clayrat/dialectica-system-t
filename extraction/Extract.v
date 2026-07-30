(** * Extraction of the Dialectica pipeline to OCaml

    The computational part of the translation — the type translation [W]/[C],
    the internal matrix [diaT], the proof translation [wit], and the composed
    pipeline [realizer := norm ∘ wit] — is total and proof-free, so it
    extracts to runnable OCaml, together with the NbE normalizer it invokes.
    This is a standalone driver, NOT part of the main build (not in
    _CoqProject).  Regenerate with (from the extraction/ dir):

        ~/.opam/rocq-9.1/bin/rocq compile \
          -Q ../nbe-system-t/theories NbE -Q ../theories SystemT Extract.v

    (or just `make extract`), which writes dialectica.ml / dialectica.mli
    here.

    What gets erased, and what doesn't:

    - Derivations [proof Γ A] are informative data (Type), so they survive as
      an ordinary OCaml variant and [wit] runs on them.  Their [Prop]
      premises — the [defeq] argument of [ax_conv], the [wtriv]/[ctriv] side
      conditions of [ax_markov]/[ax_ip] — are erased; only the proper
      subderivations and formula/term fields remain.
    - The W/C-invariance equations behind [tcast] are [Prop] ([eq]), so the
      casts extract to (at worst) [Obj.magic] identities.
    - As in the NbE extraction (see nbe-system-t's extraction/DESIGN.md for
      the full discussion): semantic values of [sem] have no OCaml type, so
      the normalizer carries [Obj.magic]; and the constructors of
      [prp]/[proof]/[tm]/[nf]/[ne] keep their context/type indices as
      ordinary fields — the data is load-bearing in type-directed NbE, and
      Coq extraction performs no forcing analysis that could drop it.

    [nat] is mapped to native [int] below, purely for readable numerals. *)

From NbE Require Import Syntax OPE NormalForms Model Subst.
From SystemT Require Import Terms HA Dialectica Realizer.
From Stdlib Require Import List Extraction.
Import ListNotations.

Extraction Language OCaml.

(* Same mapping as the NbE extraction: Coq [nat] onto native [int], with the
   eliminator clamping non-positive inputs to zero so OCaml callers cannot
   make [numeral] recurse forever on a negative. *)
Extract Inductive nat => "int" [ "0" "(fun n -> n + 1)" ]
  "(fun zero succ n -> if n <= 0 then zero () else succ (n - 1))".

Open Scope ty_scope.
Open Scope tm_scope.
Open Scope prp_scope.

(** The showcase derivations live in Dialectica.v / Realizer.v: [ex_two]
    (∃-introduction), [ex_succ] (a ∀∃ program), [mp_ex] (Markov's
    principle), [plus0] (induction).  We export their *normalized*
    realizers as [nf] constants — thunks in the extracted code, so OCaml
    runs [wit] and the extracted normalizer at module load, genuinely
    exercising the whole pipeline. *)

Definition real_two    := realizer ex_two.
Definition real_succ   := realizer ex_succ.
Definition real_markov := realizer mp_ex.
Definition real_plus0  := realizer plus0.

(** Closed instances of the Dialectica game, played entirely inside the
    object language: matrix · witness · counter, normalized.  By
    [soundness_syntactic] each must come out [ntrue] — the OCaml driver
    re-checks that with the *extracted* normalizer. *)

Definition chk_two : nf [] tBool :=
  norm (diaT (pEx (pEq v0 (numeral 2))) · wit ex_two · tunit).

Definition chk_markov : nf [] tBool :=
  norm (diaT (pEx (pEq v0 tzero)) · wit mp_ex · tunit).

Definition chk_plus0 : nf [] tBool :=
  norm (diaT (pAll (pEq (tplus · v0 · tzero) v0)) · wit plus0
        · tpair (numeral 5) tunit).

Set Extraction Output Directory ".".

(* Export the pipeline as a usable little library — formula/type translation,
   proof translation, normalizer — plus the demo derivations and the
   precomputed results the driver prints. *)
Extraction "dialectica.ml"
  W C diaT wit realizer norm nf_emb numeral tplus teqb tdefault
  ex_two ex_succ mp_ex plus0
  real_two real_succ real_markov real_plus0
  chk_two chk_markov chk_plus0.
