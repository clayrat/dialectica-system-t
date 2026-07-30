(** * Examples: executable checks of the Dialectica pipeline

    Demonstration derivations and their denotational, normal-form, validity,
    and syntactic-soundness checks.  Keeping them here leaves the translation
    ([Dialectica.v]) and the normalization/soundness interface
    ([Realizer.v]) free of clients of their APIs. *)

From Stdlib Require Import List.
Import ListNotations.
From NbE Require Import
  Syntax OPE NormalForms Model Subst DefEq Soundness Decide
  SetModel SetModelPER.
From SystemT Require Import
  Terms Semantics HA Dialectica Validity Realizer.

Open Scope ty_scope.
Open Scope tm_scope.
Open Scope prp_scope.

(** ** Elementary existential examples *)

(** [⊢ ∃y. y = 2], by [ax_ex_intro] at the numeral 2.  Note that the required
    identification of [psub1 (pEq v0 (numeral 2)) (numeral 2)] with
    [pEq (numeral 2) (numeral 2)] is definitional — substitution computes. *)
Definition ex_two : proof [] (pEx (pEq v0 (numeral 2))) :=
  ax_mp (@ax_ex_intro [] (pEq v0 (numeral 2)) (numeral 2))
        (ax_eq_refl (numeral 2)).

(** Its extracted witness evaluates to the pair (2, tt): the interpretation
    really produces the existential witness. *)
Example ex_two_val : tmden (wit ex_two) tt = (2, tt).
Proof. reflexivity. Qed.

(** [⊢ ∀x. ∃y. y = S x].  The extracted realizer is a System T program of
    type [tN ⇒ tN × tUnit] computing the successor function. *)
Definition ex_succ : proof [] (pAll (pEx (pEq v0 (tsuc v1)))) :=
  d_gen (ax_mp (@ax_ex_intro [tN] (pEq v0 (tsuc v1)) (tsuc v0))
               (ax_eq_refl (tsuc v0))).

Example ex_succ_val : tmden (wit ex_succ) tt 5 = (6, tt).
Proof. reflexivity. Qed.

(** Validity of the two examples — concrete instances of the general
    soundness theorem, retained as computational sanity checks. *)

Example ex_two_valid : valid _ (wit ex_two).
Proof. intros ρ c _ _; destruct ρ, c; reflexivity. Qed.

Example ex_succ_valid : valid _ (wit ex_succ).
Proof.
  intros ρ c _ _; destruct ρ; destruct c as [n u]; destruct u.
  exact (teqb_refl (Γ := []) tt (S n)).
Qed.

(** Their normalized realizers expose the extracted programs syntactically. *)
Example realizer_two :
  realizer ex_two = npair (nsuc (nsuc nzero)) nunit.
Proof. reflexivity. Qed.

Example realizer_succ :
  realizer ex_succ = nlam (npair (nsuc (nne (nvar vz))) nunit).
Proof. reflexivity. Qed.

Example realizer_succ_valid : valid _ (nf_emb (realizer ex_succ)) :=
  valid_realizer ex_succ.

(** The matrix of [⊢ ∃y. y = 2] at its extracted witness normalizes to
    [ntrue], as a corollary rather than by brute computation. *)
Example syn_ex_two :
  norm (diaT (pEx (pEq v0 (numeral 2))) · wit ex_two · tunit) = ntrue :=
  soundness_syntactic _ ex_two tunit.

(** ** Contraction and induction behavior *)

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

(** The induction realizer computes.  Take [Q := iszero x]; feed the backward
    search a (vacuous) premise witness and the counter [(3, tt)] against
    [∀x. Q].  The search walks down 3, 2, 1 testing the matrix [|Q[k]|]
    (i.e. running [iszero k] — false for k = 2, 1) and stops at the first
    point whose step it can blame, reporting the step counter at index 0 in
    the second component. *)
Example ex_ind_search :
  tmden (tsnd (wit (@ax_ind [] (pAtom (tiszero · v0))))) tt
        (tt, fun _ => (fun w => w, fun w c => c)) (3, tt)
  = (tt, (0, (tt, tt))).
Proof. reflexivity. Qed.

(** ** Extraction through Markov's principle

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

(** The whole path is also covered by syntactic soundness. *)
Example syn_markov :
  norm (diaT (pEx (pEq v0 tzero)) · wit mp_ex · tunit) = ntrue :=
  soundness_syntactic _ mp_ex tunit.

(** ** Extraction through Independence of Premise

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

(** ** A real induction proof

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
