(** * Realizer: arithmetic derivations to System T normal forms

    The composition of the two developments:

      - [wit]  (Dialectica.v, this repo): derivation -> System T realizer;
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

    Dialectica validity is also transferred across normalization:

      [valid A (wit d) -> valid A (nf_emb (realizer d))]

    The bridge "[tmden] respects [defeq]" is stated observationally through
    the per-type relation [EEq], so the η-rules do not demand functional
    extensionality. Together with D2's soundness theorem for [wit], it shows
    that every theorem of the extended calculus has a *normal-form* realizer
    winning its Dialectica game. Closed instances additionally satisfy
    syntactic soundness: their matrix programs normalize to [ntrue] against
    every closed counter. *)

From Stdlib Require Import List.
Import ListNotations.
From NbE Require Import
  Syntax OPE NormalForms Model Subst DefEq Soundness Decide
  SetModel SetModelPER.
From SystemT Require Import Terms Semantics HA Dialectica Validity.

Open Scope ty_scope.

(** ** The pipeline *)

Definition realizer {Γ} {A : prp Γ} (d : proof Γ A) : nf Γ (W A) :=
  norm (wit d).

(** Normalization preserves the realizer up to definitional equality
    (immediate from NbE soundness). *)
Theorem realizer_defeq : forall {Γ} {A : prp Γ} (d : proof Γ A),
  defeq Γ (W A) (nf_emb (realizer d)) (wit d).
Proof. intros Γ A d. apply NbE.Soundness.soundness. Qed.

(** ** Validity transfers across normalization

    The payoff of D2 + D2.5: the canonical (βη-normal) realizer of an HA
    theorem still wins its Dialectica game.  [NbE.Soundness.soundness] says
    the normal form is definitionally equal to [wit d]; [tmden_defeq] moves
    that to PER-related denotations; [dia_EEqE] and [Validity.soundness]
    (Dialectica) close the game. *)

Theorem valid_realizer : forall {Γ} {A : prp Γ} (d : proof Γ A),
    valid A (nf_emb (realizer d)).
Proof.
  intros Γ A d ρ c Hρ Hc.
  refine (eq_trans (dia_EEqE A ρ ρ
            (tmden (nf_emb (realizer d)) ρ) (tmden (wit d) ρ) c c Hρ
            (tmden_defeq _ _ (NbE.Soundness.soundness (wit d)) ρ ρ Hρ) Hc) _).
  exact (Validity.soundness d ρ c Hρ Hc).
Qed.

(** ** Syntactic soundness (D2.5, step 5)

    For closed instances the Dialectica game can be stated *inside the object
    language*: the matrix term itself normalizes to the literal [ntrue].
    Note there is no side condition on the counter — any closed syntactic
    counter is a legitimate move (definable values are extensional, by the
    fundamental lemma).

    Ingredients: the closed canonicity lemmas in [NbE.NormalForms] say a
    closed Boolean normal form is [ntrue] or [nfalse] (there are no closed
    neutrals), and the semantic soundness theorem is transported along
    [tmden_defeq]. *)

Theorem soundness_syntactic : forall (A : prp []) (d : proof [] A)
    (c : tm [] (C A)),
    norm (diaT A · wit d · c) = ntrue.
Proof.
  intros A d c.
  assert (Hsem : tmden (nf_emb (norm (diaT A · wit d · c))) tt = true).
  { refine (eq_trans (tmden_defeq _ _
              (NbE.Soundness.soundness (diaT A · wit d · c)) tt tt I) _).
    exact (soundness d tt (tmden c tt) I (tmden_EEqE c tt tt I)). }
  destruct (nf_closed_bool (norm (diaT A · wit d · c))) as [H | H].
  - exact H.
  - exfalso; rewrite H in Hsem; discriminate Hsem.
Qed.
