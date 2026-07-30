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
From NbE Require Import Syntax OPE NormalForms Model Subst DefEq Soundness Decide.
From SystemT Require Import Terms Eval Semantics HA Dialectica Validity.

Open Scope ty_scope.

(** ** The pipeline *)

Definition realizer {Γ} {A : prp Γ} (d : proof Γ A) : nf Γ (W A) :=
  norm (wit d).

(** Normalization preserves the realizer up to definitional equality
    (immediate from NbE soundness). *)
Theorem realizer_defeq : forall {Γ} {A : prp Γ} (d : proof Γ A),
  defeq Γ (W A) (nf_emb (realizer d)) (wit d).
Proof. intros Γ A d. apply NbE.Soundness.soundness. Qed.

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

Example realizer_succ_valid : valid _ (nf_emb (realizer ex_succ)) :=
  valid_realizer ex_succ.

(** ** Syntactic soundness (D2.5, step 5)

    For closed instances the Dialectica game can be stated *inside the object
    language*: the matrix term itself normalizes to the literal [ntrue].
    Note there is no side condition on the counter — any closed syntactic
    counter is a legitimate move (definable values are extensional, by the
    fundamental lemma).

    Ingredients: canonicity at [tBool] — a closed boolean normal form is
    [ntrue] or [nfalse] (there are no closed neutrals) — and the semantic
    soundness theorem transported along [tmden_defeq]. *)

Lemma ne_closed_empty : forall T, ne [] T -> False.
Proof.
  assert (H : forall Γ T, ne Γ T -> Γ = [] -> False).
  { intros Γ T u; induction u as
      [ Γ T x
      | Γ S T u IH v
      | Γ T z s u IH
      | Γ T vt vf u IH
      | Γ S T u IH
      | Γ S T u IH ].
    - intros HΓ; subst Γ; inversion x.
    - exact IH.
    - exact IH.
    - exact IH.
    - exact IH.
    - exact IH. }
  intros T u; exact (H [] T u eq_refl).
Qed.

Lemma nf_closed_bool : forall (n : nf [] tBool), n = ntrue \/ n = nfalse.
Proof.
  intros n.
  refine (nf_bool_ind (fun Γ n0 => Γ = [] -> n0 = ntrue \/ n0 = nfalse)
            _ _ _ [] n eq_refl).
  - intros; left; reflexivity.
  - intros; right; reflexivity.
  - intros Γ u HΓ; subst Γ; destruct (ne_closed_empty _ u).
Qed.

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

(** Instance: the matrix of [⊢ ∃y. y = 2] at its extracted witness
    normalizes to [ntrue], as a corollary rather than by brute computation. *)
Example syn_ex_two : norm (diaT (pEx (pEq v0 (numeral 2))) · wit ex_two · tunit)
                     = ntrue :=
  soundness_syntactic _ ex_two tunit.

(** ** A D3 demo: extraction through Markov's principle

    [⊢ ∃y. y = 0], proved the deliberately non-constructive way: establish
    [¬∀y. ¬(y = 0)] (instantiate the universal at 0 against reflexivity of
    equality, via [d_dni]) and conclude by [ax_markov] — whose side
    conditions on the atomic matrix are discharged by [eq_refl].  The
    extracted realizer nevertheless computes the concrete witness:
    normalization runs the counter-half of the negative proof, which
    produces the very index 0 at which the universal was refuted. *)

Definition mp_notallnot : proof [] (pNot (pAll (pNot (pEq v0 tzero)))) :=
  ax_chain (ax_all_elim (Q := pNot (pEq v0 tzero)) tzero)
           (d_dni (ax_eq_refl tzero)).

Definition mp_ex : proof [] (pEx (pEq v0 tzero)) :=
  ax_mp (ax_markov (pEq v0 tzero) eq_refl eq_refl) mp_notallnot.

Example realizer_markov : realizer mp_ex = npair nzero nunit.
Proof. reflexivity. Qed.

(** The whole new path is also covered by syntactic soundness: the matrix
    of the Markov-derived theorem normalizes to the literal [ntrue]. *)
Example syn_markov :
  norm (diaT (pEx (pEq v0 tzero)) · wit mp_ex · tunit) = ntrue :=
  soundness_syntactic _ mp_ex tunit.

(** ** A D3 demo: extraction through Independence of Premise

    Take [P(x) := x = x] and [Q(y) := y = 0].  The premise

      [⊢ (∀x. x = x) ⊃ ∃y. y = 0]

    ignores its universal assumption and returns the constructive witness
    [0].  Applying IP packages that choice into

      [⊢ ∃y. ((∀x. x = x) ⊃ y = 0)].

    This conclusion is already constructively provable; the point of the
    deliberately indirect derivation is to exercise [ax_ip_atomic] through
    the complete extraction pipeline. *)

Definition ip_zero : proof [] (pEx (pEq v0 tzero)) :=
  ax_mp (ax_ex_intro (Q := pEq v0 tzero) tzero)
        (ax_eq_refl tzero).

Definition ip_premise :
    proof [] (pAll (pEq v0 v0) ⊃ pEx (pEq v0 tzero)) :=
  ax_mp (d_K (pEx (pEq v0 tzero)) (pAll (pEq v0 v0))) ip_zero.

Definition ip_ex :
    proof [] (pEx (pwk (pAll (pEq v0 v0)) ⊃ pEq v0 tzero)) :=
  ax_mp
    (ax_ip_atomic (teqb · v0 · v0) (teqb · v0 · tzero))
    ip_premise.

(** The normalized realizer selects [y := 0].  The remaining pair realizes
    the implication: its forward map ignores a witness for [∀x. x = x] and
    returns the unique atomic witness [tt]; its backward map ignores that
    witness and the atomic counter, returning [(0, tt)] as a counter for the
    universal premise. *)
Example realizer_ip :
  realizer ip_ex =
    npair nzero
      (npair (nlam nunit)
             (nlam (nlam (npair nzero nunit)))).
Proof. reflexivity. Qed.

(** Syntactic soundness also checks the matrix of the IP-derived theorem
    against the concrete counter [(λ_. tt, tt)]. *)
Example syn_ip :
  norm (diaT (pEx (pwk (pAll (pEq v0 v0)) ⊃ pEq v0 tzero))
        · wit ip_ex · tpair (tlam tunit) tunit) = ntrue :=
  soundness_syntactic _ ip_ex (tpair (tlam tunit) tunit).

(** ** A D4 demo: a real induction proof

    [⊢ ∀x. x + 0 = x], where [tplus] recurses on its *first* argument, so
    the statement is not a conversion — it genuinely needs [ax_ind].  The
    derivation is the textbook one:

    - base [0 + 0 = 0]: reflexivity [0 = 0] transported by [ax_conv]
      along the computation [0 + 0 ≡ 0];
    - step [x + 0 = x ⊃ S x + 0 = S x]: [ax_leibniz] at the motive
      [Q(z) := S x + 0 = S z], instantiated at [t := x + 0] and [s := x].
      Its extra premise [Q(x + 0)], i.e. [S x + 0 = S (x + 0)], is again
      reflexivity transported along the computation
      [S x + 0 ≡ S (x + 0)]; [d_swap] then feeds it in.

    Every [defeq] side condition follows from [defeq_iff_norm] and
    [eq_refl]: the normalizer decides the conversion.  The [b]/[b'] pins on
    [ax_conv] are needed because the substituted atoms cannot be inferred
    by unification (they are [psub1]-computations, cf. the evar-pinning
    pattern in Validity.v). *)

Definition plus0_base : proof [] (psub1 (pEq (tplus · v0 · tzero) v0) tzero) :=
  ax_conv (b := teqb · tzero · tzero)
    (b' := teqb · (tplus · tzero · tzero) · tzero)
    ((proj2 (defeq_iff_norm
               (teqb · tzero · tzero)
               (teqb · (tplus · tzero · tzero) · tzero))) eq_refl)
    (ax_eq_refl tzero).

Definition plus0_step :
  proof [] (pAll (pEq (tplus · v0 · tzero) v0
                  ⊃ psucc (pEq (tplus · v0 · tzero) v0))) :=
  d_gen (ax_mp
           (d_swap (ax_leibniz
                      (Q := pEq (tplus · (tsuc v1) · tzero) (tsuc v0))
                      (tplus · v0 · tzero) v0))
           (ax_conv (b := teqb · (tsuc (tplus · v0 · tzero))
                        · (tsuc (tplus · v0 · tzero)))
              (b' := teqb · (tplus · (tsuc v0) · tzero)
                        · (tsuc (tplus · v0 · tzero)))
              ((proj2 (defeq_iff_norm
                 (teqb · (tsuc (tplus · v0 · tzero))
                    · (tsuc (tplus · v0 · tzero)))
                 (teqb · (tplus · (tsuc v0) · tzero)
                    · (tsuc (tplus · v0 · tzero))))) eq_refl)
              (ax_eq_refl (tsuc (tplus · v0 · tzero))))).

Definition plus0 : proof [] (pAll (pEq (tplus · v0 · tzero) v0)) :=
  ax_mp (ax_ind (Q := pEq (tplus · v0 · tzero) v0))
        (d_pair plus0_base plus0_step).

(** The extracted program: [λn. rec tt (λ_ _. tt) n] — the induction
    skeleton with all its witness content erased to units, still blocked
    on the free [n] (NbE has no η-rule at [tUnit]).  For a ∀-closure of
    atoms the program *should* be trivial: all the content of the theorem
    lives in its matrix, i.e. in validity. *)
Example realizer_plus0 :
  realizer plus0 = nlam (nne (nrec nunit (nlam (nlam nunit)) (nvar vz))).
Proof. reflexivity. Qed.

(** The object-level payoff, via [soundness_syntactic]: the matrix — the
    compiled decision procedure [eqb (n + 0) n] — normalizes to [ntrue]
    against any closed counter, e.g. the instance [n := 5]. *)
Example syn_plus0 :
  norm (diaT (pAll (pEq (tplus · v0 · tzero) v0)) · wit plus0
        · tpair (numeral 5) tunit) = ntrue :=
  soundness_syntactic _ plus0 (tpair (numeral 5) tunit).
