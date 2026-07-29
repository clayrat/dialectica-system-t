(** * Realizer: HA proofs to System T normal forms

    The composition of the two developments:

      - [wit]  (Dialectica.v, this repo): HA proof  ->  System T realizer;
      - [norm] (nbe-system-t, Model.v):   realizer  ->  βη-normal form.

    [realizer d := norm (wit d)] turns an HA derivation into a *readable*
    System T program of the witness type [W A] — the canonical (βη-normal)
    realizer among all those definitionally equal to [wit d].  This is more than cosmetic:
    higher-type realizers (every implication witness is a pair of functions)
    have no base-type readback, so normal forms are the only way to display
    them — [tmden] can only show their behavior.

    No adaptation of either side is needed for this to typecheck: the [tcast]s
    inside [wit] are meta-level and transparent, so for any concrete
    derivation [wit d] computes to a cast-free [tm]; and [wit] only produces
    saturated [trec]s, matching the neutral grammar of the normal forms.

    From the NbE metatheory we inherit, for free:
      - [realizer_defeq]: the normal form is definitionally equal (Fig. 2.2 βη)
        to the original realizer — normalization did not change the program;
      - via [defeq_iff_norm] (Decide.v), extracted realizers can be compared
        for definitional equality by deciding syntactic equality of their
        normal forms.

    Still TODO (PROGRESS.md D2.5, step 2): transfer of Dialectica *validity*
    across normalization,

      [valid A (wit d) -> valid A (nf_emb (realizer d))]

    which needs "[tmden] respects [defeq]", stated observationally (per-type
    logical relation) so that the η-rules do not demand functional
    extensionality.  It will reuse the substitution fusion lemmas of
    NbE.Subst.  Together with D2's soundness theorem for [wit], that transfer
    will show that every HA theorem has a *normal-form* realizer winning its
    Dialectica game. *)

From Stdlib Require Import List.
Import ListNotations.
From NbE Require Import Syntax OPE NormalForms Model Subst DefEq Soundness.
From SystemT Require Import Terms HA Dialectica.

Open Scope ty_scope.

(** ** The pipeline *)

Definition realizer {Γ} {A : prp Γ} (d : proof Γ A) : nf Γ (W A) :=
  norm (wit d).

(** Normalization preserves the realizer up to definitional equality
    (immediate from NbE soundness). *)
Theorem realizer_defeq : forall {Γ} {A : prp Γ} (d : proof Γ A),
  defeq Γ (W A) (nf_emb (realizer d)) (wit d).
Proof. intros Γ A d. apply soundness. Qed.

(** ** Extracted programs, now in normal form *)

(** [⊢ ∃y. y = 2]: the realizer normalizes to the literal pair (2, tt). *)
Example realizer_two :
  realizer ex_two = npair (nsuc (nsuc nzero)) nunit.
Proof. reflexivity. Qed.

(** [⊢ ∀x∃y. y = S x]: the realizer normalizes to λn. (S n, tt) — the
    successor function, read off syntactically rather than observed
    semantically as in Dialectica.v's [ex_succ_val]. *)
Example realizer_succ :
  realizer ex_succ = nlam (npair (nsuc (nne (nvar vz))) nunit).
Proof. reflexivity. Qed.

(** The identity derivation [d_id P] is [chain and_contr and_eliml], so its
    realizer routes through the contraction [P ⊃ P ∧ P] — the rule whose
    counter-half must *run the matrix* [diaT P] at evaluation time.  At
    [P := x ≐ x] (context [[tN]]), the normal form makes that visible:

      - the forward map normalizes to the identity [nlam (nne (nvar vz))];
      - the backward map normalizes to

          λw c. if (eqb x x) then tt else c

        where [eqb x x] appears as a neutral [nrec]-chain blocked on the free
        variable [x] — the compiled decision procedure sitting inside the
        extracted program, exactly as the design intends. *)
Example realizer_id_forward :
  exists g, realizer (d_id (pEq v0 v0) (Γ := [tN]))
            = npair (nlam (nne (nvar vz))) g.
Proof. eexists. reflexivity. Qed.
