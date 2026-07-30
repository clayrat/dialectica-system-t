(** * Validity: matrix semantics and realizer correctness

    Step 3 establishes the characterization of [dia] that the rest of the
    soundness proof works with — after this file, [diaT] never needs to be
    unfolded again:

    - [dia_EEqE]: the matrix respects the PER in all three arguments;
    - [dia_atom] .. [dia_ex]: one unfolding equation per formula constructor,
      in two-environment PER form;
    - [dia_pren]/[dia_psub]: the matrix of a renamed/substituted formula is
      the matrix of the original in the pushed-forward environment, modulo
      [tyden_cast] transports along [W_ren]/[W_sub]/[C_ren]/[C_sub] — the
      "cast hot spot" of the plan, discharged with the UIP-based collapse
      lemmas of [NbE.SetModelPER];
    - corollaries [dia_pwk], [dia_psub1], [dia_psucc]: the three instances
      the validity lemmas of step 6 actually consume.

    Step 5 verifies the induction realizer separately from its definition:

    - [ind_fwd]/[ind_pair] are semantic mirrors of its forward recursion and
      backward counterexample search;
    - [ind_pair_EEq] keeps the search in the PER domain, while [ind_spec]
      proves the Goedel/Bauer search invariant;
    - [r_ind_fwd_den]/[r_ind_bwd_den] connect the mirrors back to [tmden
      r_ind], and [Valid_r_ind] assembles the validity proof for induction.

    Step 6 proves validity of the remaining proof-rule realizers:

    - closed axioms, propositional combinators, and the arithmetic axioms;
    - conditional validity lemmas for rules with proof premises;
    - quantifier introduction/elimination and Leibniz substitution, using the
      renaming and substitution characterizations established in step 3.

    Step 7 assembles these lemmas by structural induction on derivations in
    the HA fragment, including atomic conversion, yielding [soundness] and
    its closed-formula specialization [soundness_closed].

    D3 extends the source calculus with quantifier-free Markov and
    universal-premise Independence of Premise.
    [Valid_r_markov_generalized] and [Valid_r_ip_generalized] validate their
    realizers; atomic compatibility corollaries recover the original
    instances, and the same [soundness] theorem covers the extended calculus.

    Atomic conversion, added with the D4 induction example, reuses the
    underlying realizer and transports validity along definitional equality
    via [tmden_defeq].

    Everything is stated over the PER domain (self-related or pairwise
    related values); unrestricted versions are not available axiom-free. *)

From Stdlib Require Import List Bool.
Import ListNotations.
From NbE Require Import Syntax OPE Subst DefEq SetModel SetModelPER.
From SystemT Require Import Terms Semantics HA Dialectica.

Open Scope ty_scope.
Open Scope tm_scope.
Open Scope prp_scope.

(** ** Denotational matrix and validity

    The Dialectica matrix, denotationally via [NbE.SetModel], and the
    interpretation proper: [A] is valid when some System T witness [t] beats
    every counter.

    Quantification is over the PER *domain* — self-related environments and
    counters — not over arbitrary values.  Under the axiom-free PER
    discipline ([NbE.SetModelPER]) this restriction is forced: the
    commutation lemmas soundness relies on only speak about values in the
    domain, and an unrestricted statement would be false — e.g. it would make every
    [F : (nat -> nat) -> nat] respect pointwise equality of its argument,
    which is exactly the extensionality we do not assume.  ([diaT] itself
    substitutes internally at quantifiers, so even reaching the boolean
    observation passes through higher-order values first.)

    The restriction is cheap where it matters:
    - closed formulas ([Γ = []]): the environment premise is trivial;
    - pure HA contexts (all [tN]): environments are tuples of numbers,
      self-related for free;
    - the witness side needs no premise: [tmden t ρ] is self-related by the
      fundamental lemma whenever [ρ] is. *)

Definition dia {Γ} (A : prp Γ) (ρ : cxtden Γ)
  (w : tyden (W A)) (c : tyden (C A)) : bool :=
  tmden (diaT A) ρ w c.

Definition valid {Γ} (A : prp Γ) (t : tm Γ (W A)) : Prop :=
  forall ρ c, EEqE Γ ρ ρ -> EEq (C A) c c ->
    dia A ρ (tmden t ρ) c = true.

(** The trivial-move fragments of HA.v mean what their name says: they
    guarantee PER-triviality of the corresponding move types. *)
Lemma wtriv_ctriv_triv : forall {Γ} (A : prp Γ),
    (wtriv A = true -> triv (W A) = true)
    /\ (ctriv A = true -> triv (C A) = true).
Proof.
  induction A as
    [ Γ b | Γ A1 IH1 A2 IH2 | Γ A1 IH1 A2 IH2 | Γ A1 IH1 A2 IH2
    | Γ A1 IH1 | Γ A1 IH1 ]; simpl; split; intros H; try discriminate.
  - reflexivity.
  - reflexivity.
  - apply andb_true_iff in H; destruct H as [H1 H2].
    rewrite (proj1 IH1 H1), (proj1 IH2 H2); reflexivity.
  - apply andb_true_iff in H; destruct H as [H1 H2].
    rewrite (proj2 IH1 H1), (proj2 IH2 H2); reflexivity.
  - apply andb_true_iff in H; destruct H as [H1 H2].
    rewrite (proj2 IH1 H1), (proj2 IH2 H2); reflexivity.
  - apply andb_true_iff in H; destruct H as [H1 H2].
    rewrite (proj1 IH2 H2), (proj2 IH1 H1); reflexivity.
  - apply andb_true_iff in H; destruct H as [H1 H2].
    rewrite (proj1 IH1 H1), (proj2 IH2 H2); reflexivity.
  - exact (proj1 IH1 H).
  - exact (proj2 IH1 H).
Qed.

(** Soundness — [forall Γ (A : prp Γ) (d : proof Γ A), valid A (wit d)] —
    is proved below ([soundness]), on top of the [tm_ren]/[subst]
    commutation lemmas of [NbE.SetModelPER], the local instances in
    [Semantics.v], and the [dia] characterization; each axiom's verification
    is the analogue of the corresponding [Theorem] of
    theories_old/intuitionistic.v, transposed to the PER discipline. *)

(** ** The matrix respects the PER *)

Lemma dia_EEqE : forall {Γ} (A : prp Γ) (ρ ρ' : cxtden Γ)
                        (w w' : tyden (W A)) (c c' : tyden (C A)),
    EEqE Γ ρ ρ' -> EEq (W A) w w' -> EEq (C A) c c' ->
    dia A ρ w c = dia A ρ' w' c'.
Proof.
  intros Γ A ρ ρ' w w' c c' Hρ Hw Hc.
  exact (tmden_EEqE (diaT A) ρ ρ' Hρ _ _ Hw _ _ Hc).
Qed.

(** ** Unfolding the matrix, constructor by constructor *)

Lemma dia_atom : forall {Γ} (b : tm Γ tBool) (ρ ρ' : cxtden Γ)
                        (w c : tyden tUnit),
    EEqE Γ ρ ρ' ->
    dia (pAtom b) ρ w c = tmden b ρ'.
Proof.
  intros Γ b ρ ρ' w c Hρ.
  exact (tmden_wk2_EEq b c c w w ρ ρ' eq_refl eq_refl Hρ).
Qed.

Lemma dia_and : forall {Γ} (B D : prp Γ) (ρ ρ' : cxtden Γ)
                       (w w' : tyden (W (B ∧ D))) (c c' : tyden (C (B ∧ D))),
    EEqE Γ ρ ρ' -> EEq (W (B ∧ D)) w w' -> EEq (C (B ∧ D)) c c' ->
    dia (B ∧ D) ρ w c
    = andb (dia B ρ' (fst w') (fst c')) (dia D ρ' (snd w') (snd c')).
Proof.
  intros Γ B D ρ ρ' w w' c c' Hρ Hw Hc.
  assert (HB : tmden (wk1 (wk1 (diaT B))) (c, (w, ρ)) (fst w) (fst c)
               = dia B ρ' (fst w') (fst c')).
  { exact (tmden_wk2_EEq (diaT B) c c' w w' ρ ρ' Hc Hw Hρ
             _ _ (proj1 Hw) _ _ (proj1 Hc)). }
  assert (HD : tmden (wk1 (wk1 (diaT D))) (c, (w, ρ)) (snd w) (snd c)
               = dia D ρ' (snd w') (snd c')).
  { exact (tmden_wk2_EEq (diaT D) c c' w w' ρ ρ' Hc Hw Hρ
             _ _ (proj2 Hw) _ _ (proj2 Hc)). }
  rewrite <- HB, <- HD; reflexivity.
Qed.

Lemma dia_or : forall {Γ} (B D : prp Γ) (ρ ρ' : cxtden Γ)
                      (w w' : tyden (W (B ∨ D))) (c c' : tyden (C (B ∨ D))),
    EEqE Γ ρ ρ' -> EEq (W (B ∨ D)) w w' -> EEq (C (B ∨ D)) c c' ->
    dia (B ∨ D) ρ w c
    = if fst w'
      then dia B ρ' (fst (snd w')) (fst c')
      else dia D ρ' (snd (snd w')) (snd c').
Proof.
  intros Γ B D ρ ρ' w w' c c' Hρ Hw Hc.
  assert (Hflag : fst w = fst w') by exact (proj1 Hw).
  assert (HB : tmden (wk1 (wk1 (diaT B))) (c, (w, ρ)) (fst (snd w)) (fst c)
               = dia B ρ' (fst (snd w')) (fst c')).
  { exact (tmden_wk2_EEq (diaT B) c c' w w' ρ ρ' Hc Hw Hρ
             _ _ (proj1 (proj2 Hw)) _ _ (proj1 Hc)). }
  assert (HD : tmden (wk1 (wk1 (diaT D))) (c, (w, ρ)) (snd (snd w)) (snd c)
               = dia D ρ' (snd (snd w')) (snd c')).
  { exact (tmden_wk2_EEq (diaT D) c c' w w' ρ ρ' Hc Hw Hρ
             _ _ (proj2 (proj2 Hw)) _ _ (proj2 Hc)). }
  rewrite <- HB, <- HD, <- Hflag; reflexivity.
Qed.

Lemma dia_imp : forall {Γ} (B D : prp Γ) (ρ ρ' : cxtden Γ)
                       (w w' : tyden (W (B ⊃ D))) (c c' : tyden (C (B ⊃ D))),
    EEqE Γ ρ ρ' -> EEq (W (B ⊃ D)) w w' -> EEq (C (B ⊃ D)) c c' ->
    dia (B ⊃ D) ρ w c
    = implb (dia B ρ' (fst c') (snd w' (fst c') (snd c')))
            (dia D ρ' (fst w' (fst c')) (snd c')).
Proof.
  intros Γ B D ρ ρ' w w' c c' Hρ Hw Hc.
  assert (HB : tmden (wk1 (wk1 (diaT B))) (c, (w, ρ))
                     (fst c) (snd w (fst c) (snd c))
               = dia B ρ' (fst c') (snd w' (fst c') (snd c'))).
  { exact (tmden_wk2_EEq (diaT B) c c' w w' ρ ρ' Hc Hw Hρ
             _ _ (proj1 Hc)
             _ _ (proj2 Hw _ _ (proj1 Hc) _ _ (proj2 Hc))). }
  assert (HD : tmden (wk1 (wk1 (diaT D))) (c, (w, ρ))
                     (fst w (fst c)) (snd c)
               = dia D ρ' (fst w' (fst c')) (snd c')).
  { exact (tmden_wk2_EEq (diaT D) c c' w w' ρ ρ' Hc Hw Hρ
             _ _ (proj1 Hw _ _ (proj1 Hc)) _ _ (proj2 Hc)). }
  exact (f_equal2 implb HB HD).
Qed.

Lemma dia_all : forall {Γ} (B : prp (tN :: Γ)) (ρ ρ' : cxtden Γ)
                       (w w' : tyden (W (pAll B))) (c c' : tyden (C (pAll B))),
    EEqE Γ ρ ρ' -> EEq (W (pAll B)) w w' -> EEq (C (pAll B)) c c' ->
    dia (pAll B) ρ w c = dia B (fst c', ρ') (w' (fst c')) (snd c').
Proof.
  intros Γ B ρ ρ' w w' c c' Hρ Hw Hc.
  assert (Henv : EEqE (tN :: Γ)
                   (subden (sub_at0 (drop_prefix [_; _]) (tfst v0)) (c', (w', ρ')))
                   (fst c', ρ')).
  { pose proof (subden_sub_at0 (drop_prefix [_; _]) (tfst v0) (c', (w', ρ')) (c', (w', ρ'))
                  (conj (EEq_refl_r _ _ _ Hc)
                        (conj (EEq_refl_r _ _ _ Hw)
                              (EEqE_refl_r _ _ _ Hρ)))) as H2.
    rewrite opeden_drop_prefix in H2; exact H2. }
  assert (Harr : EEq (W B ⇒ C B ⇒ tBool)
                   (tmden (subst (sub_at0 (drop_prefix [_; _]) (tfst v0)) (diaT B)) (c, (w, ρ)))
                   (tmden (diaT B) (fst c', ρ'))).
  { apply EEq_trans with
      (b := tmden (diaT B) (subden (sub_at0 (drop_prefix [_; _]) (tfst v0)) (c', (w', ρ')))).
    - exact (tmden_subst (diaT B) (sub_at0 (drop_prefix [_; _]) (tfst v0))
               (c, (w, ρ)) (c', (w', ρ')) (conj Hc (conj Hw Hρ))).
    - exact (tmden_EEqE (diaT B) _ _ Henv). }
  assert (H : tmden (subst (sub_at0 (drop_prefix [_; _]) (tfst v0)) (diaT B)) (c, (w, ρ))
                    (w (fst c)) (snd c)
              = dia B (fst c', ρ') (w' (fst c')) (snd c')).
  { exact (Harr _ _ (Hw _ _ (proj1 Hc)) _ _ (proj2 Hc)). }
  exact H.
Qed.

Lemma dia_ex : forall {Γ} (B : prp (tN :: Γ)) (ρ ρ' : cxtden Γ)
                      (w w' : tyden (W (pEx B))) (c c' : tyden (C (pEx B))),
    EEqE Γ ρ ρ' -> EEq (W (pEx B)) w w' -> EEq (C (pEx B)) c c' ->
    dia (pEx B) ρ w c = dia B (fst w', ρ') (snd w') c'.
Proof.
  intros Γ B ρ ρ' w w' c c' Hρ Hw Hc.
  assert (Henv : EEqE (tN :: Γ)
                   (subden (sub_at0 (drop_prefix [_; _]) (tfst v1)) (c', (w', ρ')))
                   (fst w', ρ')).
  { pose proof (subden_sub_at0 (drop_prefix [_; _]) (tfst v1) (c', (w', ρ')) (c', (w', ρ'))
                  (conj (EEq_refl_r _ _ _ Hc)
                        (conj (EEq_refl_r _ _ _ Hw)
                              (EEqE_refl_r _ _ _ Hρ)))) as H2.
    rewrite opeden_drop_prefix in H2; exact H2. }
  assert (Harr : EEq (W B ⇒ C B ⇒ tBool)
                   (tmden (subst (sub_at0 (drop_prefix [_; _]) (tfst v1)) (diaT B)) (c, (w, ρ)))
                   (tmden (diaT B) (fst w', ρ'))).
  { apply EEq_trans with
      (b := tmden (diaT B) (subden (sub_at0 (drop_prefix [_; _]) (tfst v1)) (c', (w', ρ')))).
    - exact (tmden_subst (diaT B) (sub_at0 (drop_prefix [_; _]) (tfst v1))
               (c, (w, ρ)) (c', (w', ρ')) (conj Hc (conj Hw Hρ))).
    - exact (tmden_EEqE (diaT B) _ _ Henv). }
  assert (H : tmden (subst (sub_at0 (drop_prefix [_; _]) (tfst v1)) (diaT B)) (c, (w, ρ))
                    (snd w) c
              = dia B (fst w', ρ') (snd w') c').
  { exact (Harr _ _ (proj2 Hw) _ _ Hc). }
  exact H.
Qed.

(** ** The matrix under formula substitution and renaming

    The cast hot spot.  Strategy per constructor: unfold both sides with the
    [dia_*] equations, push the [tyden_cast]s through products/arrows with
    the UIP-collapse lemmas (choosing as component proofs exactly the
    [W_sub]/[C_sub]/[W_ren]/[C_ren] instances the induction hypotheses
    produce), and close with the IHs plus [dia_EEqE] for the binder
    environments. *)

Lemma dia_psub : forall {Γ} (A : prp Γ) {Δ} (σ : sub Δ Γ) (ρ ρ' : cxtden Δ)
                        (w w' : tyden (W (psub σ A))) (c c' : tyden (C (psub σ A))),
    EEqE Δ ρ ρ' -> EEq (W (psub σ A)) w w' -> EEq (C (psub σ A)) c c' ->
    dia (psub σ A) ρ w c
    = dia A (subden σ ρ')
          (tyden_cast (W_sub σ A) w') (tyden_cast (C_sub σ A) c').
Proof.
  intros Γ A; induction A as
    [ Γ b | Γ A1 IH1 A2 IH2 | Γ A1 IH1 A2 IH2 | Γ A1 IH1 A2 IH2
    | Γ A1 IH1 | Γ A1 IH1 ];
    intros Δ σ ρ ρ' w w' c c' Hρ Hw Hc;
    pose proof (EEqE_refl_r _ _ _ Hρ) as Hρ';
    pose proof (EEq_refl_r _ _ _ Hw) as Hw';
    pose proof (EEq_refl_r _ _ _ Hc) as Hc';
    pose proof (subden_EEqE σ _ _ Hρ') as Hsub.
  - (* pAtom *)
    etransitivity.
    { exact (dia_atom (subst σ b) ρ ρ' w c Hρ). }
    etransitivity.
    { exact (tmden_subst b σ ρ' ρ' Hρ'). }
    symmetry.
    exact (dia_atom b (subden σ ρ') (subden σ ρ') _ _ Hsub).
  - (* pAnd *)
    etransitivity.
    { exact (dia_and (psub σ A1) (psub σ A2) ρ ρ' w w' c c' Hρ Hw Hc). }
    etransitivity.
    { exact (f_equal2 andb
        (IH1 _ σ ρ' ρ' (fst w') (fst w') (fst c') (fst c')
           Hρ' (proj1 Hw') (proj1 Hc'))
        (IH2 _ σ ρ' ρ' (snd w') (snd w') (snd c') (snd c')
           Hρ' (proj2 Hw') (proj2 Hc'))). }
    symmetry.
    etransitivity.
    { exact (dia_and A1 A2 (subden σ ρ') (subden σ ρ') _ _ _ _
               Hsub (EEq_cast _ _ _ Hw') (EEq_cast _ _ _ Hc')). }
    rewrite (tyden_cast_prod_fst (W_sub σ A1) (W_sub σ A2)).
    rewrite (tyden_cast_prod_snd (W_sub σ A1) (W_sub σ A2)).
    rewrite (tyden_cast_prod_fst (C_sub σ A1) (C_sub σ A2)).
    rewrite (tyden_cast_prod_snd (C_sub σ A1) (C_sub σ A2)).
    reflexivity.
  - (* pOr *)
    assert (eW2 : (W (psub σ A1) × W (psub σ A2)) = (W A1 × W A2))
      by (rewrite (W_sub σ A1), (W_sub σ A2); reflexivity).
    etransitivity.
    { exact (dia_or (psub σ A1) (psub σ A2) ρ ρ' w w' c c' Hρ Hw Hc). }
    etransitivity.
    { exact (f_equal3 (fun (b : bool) (x y : bool) => if b then x else y)
        (eq_refl (fst w'))
        (IH1 _ σ ρ' ρ' (fst (snd w')) (fst (snd w')) (fst c') (fst c')
           Hρ' (proj1 (proj2 Hw')) (proj1 Hc'))
        (IH2 _ σ ρ' ρ' (snd (snd w')) (snd (snd w')) (snd c') (snd c')
           Hρ' (proj2 (proj2 Hw')) (proj2 Hc'))). }
    symmetry.
    etransitivity.
    { exact (dia_or A1 A2 (subden σ ρ') (subden σ ρ') _ _ _ _
               Hsub (EEq_cast _ _ _ Hw') (EEq_cast _ _ _ Hc')). }
    rewrite (tyden_cast_prod_fst (@eq_refl ty tBool) eW2).
    rewrite (tyden_cast_prod_snd (@eq_refl ty tBool) eW2).
    rewrite tyden_cast_refl.
    rewrite (tyden_cast_prod_fst (W_sub σ A1) (W_sub σ A2)).
    rewrite (tyden_cast_prod_snd (W_sub σ A1) (W_sub σ A2)).
    rewrite (tyden_cast_prod_fst (C_sub σ A1) (C_sub σ A2)).
    rewrite (tyden_cast_prod_snd (C_sub σ A1) (C_sub σ A2)).
    reflexivity.
  - (* pImp *)
    assert (eW1 : (W (psub σ A1) ⇒ W (psub σ A2)) = (W A1 ⇒ W A2))
      by (rewrite (W_sub σ A1), (W_sub σ A2); reflexivity).
    assert (eCB : (C (psub σ A2) ⇒ C (psub σ A1)) = (C A2 ⇒ C A1))
      by (rewrite (C_sub σ A1), (C_sub σ A2); reflexivity).
    assert (eW2 : (W (psub σ A1) ⇒ C (psub σ A2) ⇒ C (psub σ A1))
                  = (W A1 ⇒ C A2 ⇒ C A1))
      by (rewrite (W_sub σ A1), (C_sub σ A1), (C_sub σ A2); reflexivity).
    etransitivity.
    { exact (dia_imp (psub σ A1) (psub σ A2) ρ ρ' w w' c c' Hρ Hw Hc). }
    etransitivity.
    { exact (f_equal2 implb
        (IH1 _ σ ρ' ρ' (fst c') (fst c')
           (snd w' (fst c') (snd c')) (snd w' (fst c') (snd c'))
           Hρ' (proj1 Hc')
           (proj2 Hw' _ _ (proj1 Hc') _ _ (proj2 Hc')))
        (IH2 _ σ ρ' ρ' (fst w' (fst c')) (fst w' (fst c')) (snd c') (snd c')
           Hρ' (proj1 Hw' _ _ (proj1 Hc')) (proj2 Hc'))). }
    symmetry.
    etransitivity.
    { exact (dia_imp A1 A2 (subden σ ρ') (subden σ ρ') _ _ _ _
               Hsub (EEq_cast _ _ _ Hw') (EEq_cast _ _ _ Hc')). }
    rewrite (tyden_cast_prod_fst eW1 eW2).
    rewrite (tyden_cast_prod_snd eW1 eW2).
    rewrite (tyden_cast_prod_fst (W_sub σ A1) (C_sub σ A2)).
    rewrite (tyden_cast_prod_snd (W_sub σ A1) (C_sub σ A2)).
    rewrite (tyden_cast_arr (W_sub σ A1) (W_sub σ A2) eW1).
    rewrite (tyden_cast_arr (W_sub σ A1) eCB eW2).
    rewrite (tyden_cast_arr (C_sub σ A2) (C_sub σ A1) eCB).
    rewrite !tyden_cast_sym_cancel.
    reflexivity.
  - (* pAll *)
    etransitivity.
    { exact (dia_all (psub (sub_lift σ) A1) ρ ρ' w w' c c' Hρ Hw Hc). }
    etransitivity.
    { exact (IH1 _ (sub_lift σ) (fst c', ρ') (fst c', ρ')
               (w' (fst c')) (w' (fst c')) (snd c') (snd c')
               (conj eq_refl Hρ') (Hw' _ _ eq_refl) (proj2 Hc')). }
    symmetry.
    etransitivity.
    { exact (dia_all A1 (subden σ ρ') (subden σ ρ') _ _ _ _
               Hsub (EEq_cast _ _ _ Hw') (EEq_cast _ _ _ Hc')). }
    rewrite (tyden_cast_prod_fst (@eq_refl ty tN) (C_sub (sub_lift σ) A1)).
    rewrite (tyden_cast_prod_snd (@eq_refl ty tN) (C_sub (sub_lift σ) A1)).
    rewrite tyden_cast_refl.
    rewrite (tyden_cast_arr (@eq_refl ty tN) (W_sub (sub_lift σ) A1)).
    rewrite tyden_cast_refl.
    apply dia_EEqE.
    + exact (EEqE_sym _ _ _
               (subden_sub_lift (S := tN) σ (fst c') (fst c') ρ' ρ' eq_refl Hρ')).
    + exact (EEq_cast _ _ _ (Hw' _ _ eq_refl)).
    + exact (EEq_cast _ _ _ (proj2 Hc')).
  - (* pEx *)
    etransitivity.
    { exact (dia_ex (psub (sub_lift σ) A1) ρ ρ' w w' c c' Hρ Hw Hc). }
    etransitivity.
    { exact (IH1 _ (sub_lift σ) (fst w', ρ') (fst w', ρ')
               (snd w') (snd w') c' c'
               (conj eq_refl Hρ') (proj2 Hw') Hc'). }
    symmetry.
    etransitivity.
    { exact (dia_ex A1 (subden σ ρ') (subden σ ρ') _ _ _ _
               Hsub (EEq_cast _ _ _ Hw') (EEq_cast _ _ _ Hc')). }
    rewrite (tyden_cast_prod_fst (@eq_refl ty tN) (W_sub (sub_lift σ) A1)).
    rewrite (tyden_cast_prod_snd (@eq_refl ty tN) (W_sub (sub_lift σ) A1)).
    rewrite tyden_cast_refl.
    rewrite (ty_uip (C_sub σ (pEx A1)) (C_sub (sub_lift σ) A1)).
    apply dia_EEqE.
    + exact (EEqE_sym _ _ _
               (subden_sub_lift (S := tN) σ (fst w') (fst w') ρ' ρ' eq_refl Hρ')).
    + exact (EEq_cast _ _ _ (proj2 Hw')).
    + exact (EEq_cast _ _ _ Hc').
Qed.

Lemma dia_pren : forall {Γ} (A : prp Γ) {Δ} (o : ope Δ Γ) (ρ ρ' : cxtden Δ)
                        (w w' : tyden (W (pren o A))) (c c' : tyden (C (pren o A))),
    EEqE Δ ρ ρ' -> EEq (W (pren o A)) w w' -> EEq (C (pren o A)) c c' ->
    dia (pren o A) ρ w c
    = dia A (opeden o ρ')
          (tyden_cast (W_ren o A) w') (tyden_cast (C_ren o A) c').
Proof.
  intros Γ A; induction A as
    [ Γ b | Γ A1 IH1 A2 IH2 | Γ A1 IH1 A2 IH2 | Γ A1 IH1 A2 IH2
    | Γ A1 IH1 | Γ A1 IH1 ];
    intros Δ o ρ ρ' w w' c c' Hρ Hw Hc;
    pose proof (EEqE_refl_r _ _ _ Hρ) as Hρ';
    pose proof (EEq_refl_r _ _ _ Hw) as Hw';
    pose proof (EEq_refl_r _ _ _ Hc) as Hc';
    pose proof (opeden_EEqE o _ _ Hρ') as Hope.
  - (* pAtom *)
    etransitivity.
    { exact (dia_atom (tm_ren o b) ρ ρ' w c Hρ). }
    etransitivity.
    { exact (tmden_tm_ren b o ρ' ρ' Hρ'). }
    symmetry.
    exact (dia_atom b (opeden o ρ') (opeden o ρ') _ _ Hope).
  - (* pAnd *)
    etransitivity.
    { exact (dia_and (pren o A1) (pren o A2) ρ ρ' w w' c c' Hρ Hw Hc). }
    etransitivity.
    { exact (f_equal2 andb
        (IH1 _ o ρ' ρ' (fst w') (fst w') (fst c') (fst c')
           Hρ' (proj1 Hw') (proj1 Hc'))
        (IH2 _ o ρ' ρ' (snd w') (snd w') (snd c') (snd c')
           Hρ' (proj2 Hw') (proj2 Hc'))). }
    symmetry.
    etransitivity.
    { exact (dia_and A1 A2 (opeden o ρ') (opeden o ρ') _ _ _ _
               Hope (EEq_cast _ _ _ Hw') (EEq_cast _ _ _ Hc')). }
    rewrite (tyden_cast_prod_fst (W_ren o A1) (W_ren o A2)).
    rewrite (tyden_cast_prod_snd (W_ren o A1) (W_ren o A2)).
    rewrite (tyden_cast_prod_fst (C_ren o A1) (C_ren o A2)).
    rewrite (tyden_cast_prod_snd (C_ren o A1) (C_ren o A2)).
    reflexivity.
  - (* pOr *)
    assert (eW2 : (W (pren o A1) × W (pren o A2)) = (W A1 × W A2))
      by (rewrite (W_ren o A1), (W_ren o A2); reflexivity).
    etransitivity.
    { exact (dia_or (pren o A1) (pren o A2) ρ ρ' w w' c c' Hρ Hw Hc). }
    etransitivity.
    { exact (f_equal3 (fun (b : bool) (x y : bool) => if b then x else y)
        (eq_refl (fst w'))
        (IH1 _ o ρ' ρ' (fst (snd w')) (fst (snd w')) (fst c') (fst c')
           Hρ' (proj1 (proj2 Hw')) (proj1 Hc'))
        (IH2 _ o ρ' ρ' (snd (snd w')) (snd (snd w')) (snd c') (snd c')
           Hρ' (proj2 (proj2 Hw')) (proj2 Hc'))). }
    symmetry.
    etransitivity.
    { exact (dia_or A1 A2 (opeden o ρ') (opeden o ρ') _ _ _ _
               Hope (EEq_cast _ _ _ Hw') (EEq_cast _ _ _ Hc')). }
    rewrite (tyden_cast_prod_fst (@eq_refl ty tBool) eW2).
    rewrite (tyden_cast_prod_snd (@eq_refl ty tBool) eW2).
    rewrite tyden_cast_refl.
    rewrite (tyden_cast_prod_fst (W_ren o A1) (W_ren o A2)).
    rewrite (tyden_cast_prod_snd (W_ren o A1) (W_ren o A2)).
    rewrite (tyden_cast_prod_fst (C_ren o A1) (C_ren o A2)).
    rewrite (tyden_cast_prod_snd (C_ren o A1) (C_ren o A2)).
    reflexivity.
  - (* pImp *)
    assert (eW1 : (W (pren o A1) ⇒ W (pren o A2)) = (W A1 ⇒ W A2))
      by (rewrite (W_ren o A1), (W_ren o A2); reflexivity).
    assert (eCB : (C (pren o A2) ⇒ C (pren o A1)) = (C A2 ⇒ C A1))
      by (rewrite (C_ren o A1), (C_ren o A2); reflexivity).
    assert (eW2 : (W (pren o A1) ⇒ C (pren o A2) ⇒ C (pren o A1))
                  = (W A1 ⇒ C A2 ⇒ C A1))
      by (rewrite (W_ren o A1), (C_ren o A1), (C_ren o A2); reflexivity).
    etransitivity.
    { exact (dia_imp (pren o A1) (pren o A2) ρ ρ' w w' c c' Hρ Hw Hc). }
    etransitivity.
    { exact (f_equal2 implb
        (IH1 _ o ρ' ρ' (fst c') (fst c')
           (snd w' (fst c') (snd c')) (snd w' (fst c') (snd c'))
           Hρ' (proj1 Hc')
           (proj2 Hw' _ _ (proj1 Hc') _ _ (proj2 Hc')))
        (IH2 _ o ρ' ρ' (fst w' (fst c')) (fst w' (fst c')) (snd c') (snd c')
           Hρ' (proj1 Hw' _ _ (proj1 Hc')) (proj2 Hc'))). }
    symmetry.
    etransitivity.
    { exact (dia_imp A1 A2 (opeden o ρ') (opeden o ρ') _ _ _ _
               Hope (EEq_cast _ _ _ Hw') (EEq_cast _ _ _ Hc')). }
    rewrite (tyden_cast_prod_fst eW1 eW2).
    rewrite (tyden_cast_prod_snd eW1 eW2).
    rewrite (tyden_cast_prod_fst (W_ren o A1) (C_ren o A2)).
    rewrite (tyden_cast_prod_snd (W_ren o A1) (C_ren o A2)).
    rewrite (tyden_cast_arr (W_ren o A1) (W_ren o A2) eW1).
    rewrite (tyden_cast_arr (W_ren o A1) eCB eW2).
    rewrite (tyden_cast_arr (C_ren o A2) (C_ren o A1) eCB).
    rewrite !tyden_cast_sym_cancel.
    reflexivity.
  - (* pAll *)
    etransitivity.
    { exact (dia_all (pren (ope_keep o) A1) ρ ρ' w w' c c' Hρ Hw Hc). }
    etransitivity.
    { exact (IH1 _ (ope_keep o) (fst c', ρ') (fst c', ρ')
               (w' (fst c')) (w' (fst c')) (snd c') (snd c')
               (conj eq_refl Hρ') (Hw' _ _ eq_refl) (proj2 Hc')). }
    symmetry.
    etransitivity.
    { exact (dia_all A1 (opeden o ρ') (opeden o ρ') _ _ _ _
               Hope (EEq_cast _ _ _ Hw') (EEq_cast _ _ _ Hc')). }
    rewrite (tyden_cast_prod_fst (@eq_refl ty tN) (C_ren (ope_keep o) A1)).
    rewrite (tyden_cast_prod_snd (@eq_refl ty tN) (C_ren (ope_keep o) A1)).
    rewrite tyden_cast_refl.
    rewrite (tyden_cast_arr (@eq_refl ty tN) (W_ren (ope_keep o) A1)).
    rewrite tyden_cast_refl.
    reflexivity.
  - (* pEx *)
    etransitivity.
    { exact (dia_ex (pren (ope_keep o) A1) ρ ρ' w w' c c' Hρ Hw Hc). }
    etransitivity.
    { exact (IH1 _ (ope_keep o) (fst w', ρ') (fst w', ρ')
               (snd w') (snd w') c' c'
               (conj eq_refl Hρ') (proj2 Hw') Hc'). }
    symmetry.
    etransitivity.
    { exact (dia_ex A1 (opeden o ρ') (opeden o ρ') _ _ _ _
               Hope (EEq_cast _ _ _ Hw') (EEq_cast _ _ _ Hc')). }
    rewrite (tyden_cast_prod_fst (@eq_refl ty tN) (W_ren (ope_keep o) A1)).
    rewrite (tyden_cast_prod_snd (@eq_refl ty tN) (W_ren (ope_keep o) A1)).
    rewrite tyden_cast_refl.
    rewrite (ty_uip (C_ren o (pEx A1)) (C_ren (ope_keep o) A1)).
    reflexivity.
Qed.

(** ** The instances step 6 consumes *)

(** Weakened formula, extended environment. *)
Corollary dia_pwk : forall {Γ S} (A : prp Γ) (v v' : tyden S)
                           (ρ ρ' : cxtden Γ)
                           (w w' : tyden (W (pwk A))) (c c' : tyden (C (pwk A))),
    EEq S v v' -> EEqE Γ ρ ρ' ->
    EEq (W (pwk A)) w w' -> EEq (C (pwk A)) c c' ->
    dia (pwk (S := S) A) (v, ρ) w c
    = dia A ρ' (tyden_cast (W_ren wk A) w') (tyden_cast (C_ren wk A) c').
Proof.
  intros Γ S A v v' ρ ρ' w w' c c' Hv Hρ Hw Hc.
  etransitivity.
  { exact (dia_pren A wk (v, ρ) (v', ρ') w w' c c' (conj Hv Hρ) Hw Hc). }
  rewrite opeden_wk; reflexivity.
Qed.

(** Instantiated formula, environment extension by the term's value. *)
Corollary dia_psub1 : forall {Γ} (A : prp (tN :: Γ)) (t : tm Γ tN)
                             (ρ ρ' : cxtden Γ)
                             (w w' : tyden (W (psub1 A t)))
                             (c c' : tyden (C (psub1 A t))),
    EEqE Γ ρ ρ' -> EEq (W (psub1 A t)) w w' -> EEq (C (psub1 A t)) c c' ->
    dia (psub1 A t) ρ w c
    = dia A (tmden t ρ', ρ')
          (tyden_cast (W_sub (scons t) A) w') (tyden_cast (C_sub (scons t) A) c').
Proof.
  intros Γ A t ρ ρ' w w' c c' Hρ Hw Hc.
  etransitivity.
  { exact (dia_psub A (scons t) ρ ρ' w w' c c' Hρ Hw Hc). }
  apply dia_EEqE.
  - exact (subden_scons t ρ' ρ' (EEqE_refl_r _ _ _ Hρ)).
  - exact (EEq_cast _ _ _ (EEq_refl_r _ _ _ Hw)).
  - exact (EEq_cast _ _ _ (EEq_refl_r _ _ _ Hc)).
Qed.

(** Successor-substituted formula, successor environment. *)
Corollary dia_psucc : forall {Γ} (A : prp (tN :: Γ)) (ρ ρ' : cxtden (tN :: Γ))
                             (w w' : tyden (W (psucc A)))
                             (c c' : tyden (C (psucc A))),
    EEqE (tN :: Γ) ρ ρ' -> EEq (W (psucc A)) w w' -> EEq (C (psucc A)) c c' ->
    dia (psucc A) ρ w c
    = dia A (S (fst ρ'), snd ρ')
          (tyden_cast (W_sub sub_succ A) w') (tyden_cast (C_sub sub_succ A) c').
Proof.
  intros Γ A ρ ρ' w w' c c' Hρ Hw Hc.
  etransitivity.
  { exact (dia_psub A sub_succ ρ ρ' w w' c c' Hρ Hw Hc). }
  apply dia_EEqE.
  - exact (subden_sub_succ ρ' ρ' (EEqE_refl_r _ _ _ Hρ)).
  - exact (EEq_cast _ _ _ (EEq_refl_r _ _ _ Hw)).
  - exact (EEq_cast _ _ _ (EEq_refl_r _ _ _ Hc)).
Qed.

(** ** D2 step 5: the induction realizer, semantically

    [r_ind]'s two components, mirrored as canonical Coq values: [ind_fwd] is
    the primitive recursion on witnesses, [ind_pair] the recursion computing
    the pair (witness at k, searched counter from k) that the backward map
    projects.  The search spec [ind_spec] is Goedel's/Bauer's argument: if
    the premise matrix survives the searched counter, the conclusion matrix
    holds — by induction on the bound.  Definition and verification stay
    separate (the Agda-port lesson); the bridge from [tmden r_ind] to these
    mirrors is step 5d. *)

Section IndSem.
  Context {Γ : cxt} (Q : prp (tN :: Γ)).

  Local Notation P0 := (psub1 Q tzero).
  Local Notation QS := (psucc Q).
  Local Notation prem := (P0 ∧ pAll (Q ⊃ QS)).
  Local Notation eW0 := (W_sub (scons tzero) Q).
  Local Notation eC0 := (C_sub (scons tzero) Q).
  Local Notation eWS := (W_sub sub_succ Q).
  Local Notation eCS := (C_sub sub_succ Q).

  Definition ind_fwd (p : tyden (W prem)) (n : nat) : tyden (W Q) :=
    nat_rect (fun _ => tyden (W Q))
      (tyden_cast eW0 (fst p))
      (fun k r => tyden_cast eWS (fst (snd p k) r)) n.

  Definition ind_pair (ρ : cxtden Γ) (p : tyden (W prem)) (n : nat)
    : tyden (W Q × (C Q ⇒ C prem)) :=
    nat_rect (fun _ => tyden (W Q × (C Q ⇒ C prem)))
      ( tyden_cast eW0 (fst p),
        fun c => (tyden_cast (eq_sym eC0) c,
                  (0, (tydefault (W Q), tydefault (C QS)))) )
      (fun k h =>
        ( tyden_cast eWS (fst (snd p k) (fst h)),
          fun c =>
            let cS := tyden_cast (eq_sym eCS) c in
            let c' := snd (snd p k) (fst h) cS in
            if dia Q (k, ρ) (fst h) c'
            then (tydefault (C P0), (k, (fst h, cS)))
            else snd h c' )) n.

  (** The witness half of the pair is the forward recursion. *)
  Lemma ind_fwd_pair : forall ρ p n, fst (ind_pair ρ p n) = ind_fwd p n.
  Proof.
    intros ρ p n; induction n as [| k IH].
    - reflexivity.
    - change (tyden_cast eWS (fst (snd p k) (fst (ind_pair ρ p k)))
              = tyden_cast eWS (fst (snd p k) (ind_fwd p k))).
      rewrite IH; reflexivity.
  Qed.

  (** The pair stays in the PER domain. *)
  Lemma ind_pair_EEq : forall ρ p,
      EEqE Γ ρ ρ -> EEq (W prem) p p ->
      forall n, EEq (W Q × (C Q ⇒ C prem)) (ind_pair ρ p n) (ind_pair ρ p n).
  Proof.
    intros ρ p Hρ Hp n; induction n as [| k IH].
    - split.
      + exact (EEq_cast _ _ _ (proj1 Hp)).
      + intros c c' Hc; split; [exact (EEq_cast _ _ _ Hc) |].
        split; [reflexivity |].
        split; [exact (tydefault_EEq (W Q)) | exact (tydefault_EEq (C QS))].
    - assert (HW : EEq (W Q)
          (tyden_cast eWS (fst (snd p k) (fst (ind_pair ρ p k))))
          (tyden_cast eWS (fst (snd p k) (fst (ind_pair ρ p k))))).
      { exact (EEq_cast _ _ _
                 (proj1 (proj2 Hp k k eq_refl) _ _ (proj1 IH))). }
      assert (HG : forall c c', EEq (C Q) c c' ->
          EEq (C prem)
            (if dia Q (k, ρ) (fst (ind_pair ρ p k))
                  (snd (snd p k) (fst (ind_pair ρ p k))
                     (tyden_cast (eq_sym eCS) c))
             then (tydefault (C P0),
                   (k, (fst (ind_pair ρ p k), tyden_cast (eq_sym eCS) c)))
             else snd (ind_pair ρ p k)
                    (snd (snd p k) (fst (ind_pair ρ p k))
                       (tyden_cast (eq_sym eCS) c)))
            (if dia Q (k, ρ) (fst (ind_pair ρ p k))
                  (snd (snd p k) (fst (ind_pair ρ p k))
                     (tyden_cast (eq_sym eCS) c'))
             then (tydefault (C P0),
                   (k, (fst (ind_pair ρ p k), tyden_cast (eq_sym eCS) c')))
             else snd (ind_pair ρ p k)
                    (snd (snd p k) (fst (ind_pair ρ p k))
                       (tyden_cast (eq_sym eCS) c')))).
      { intros c c' Hc.
        assert (HcS := EEq_cast (eq_sym eCS) _ _ Hc).
        assert (Hc' := proj2 (proj2 Hp k k eq_refl) _ _ (proj1 IH) _ _ HcS).
        assert (Hcond : dia Q (k, ρ) (fst (ind_pair ρ p k))
                          (snd (snd p k) (fst (ind_pair ρ p k))
                             (tyden_cast (eq_sym eCS) c))
                        = dia Q (k, ρ) (fst (ind_pair ρ p k))
                            (snd (snd p k) (fst (ind_pair ρ p k))
                               (tyden_cast (eq_sym eCS) c'))).
        { exact (dia_EEqE Q (k, ρ) (k, ρ) _ _ _ _
                   (conj eq_refl Hρ) (proj1 IH) Hc'). }
        rewrite Hcond; clear Hcond.
        destruct (dia Q (k, ρ) (fst (ind_pair ρ p k))
                    (snd (snd p k) (fst (ind_pair ρ p k))
                       (tyden_cast (eq_sym eCS) c'))).
        * split; [exact (tydefault_EEq (C P0)) |].
          split; [reflexivity |].
          split; [exact (proj1 IH) | exact HcS].
        * exact (proj2 IH _ _ Hc'). }
      exact (conj HW HG).
  Qed.

  (** The search specification (Goedel/Bauer): if the premise matrix
      survives the searched counter, the conclusion matrix holds at [n]. *)
  Lemma ind_spec : forall ρ p,
      EEqE Γ ρ ρ -> EEq (W prem) p p ->
      forall n (c : tyden (C Q)), EEq (C Q) c c ->
      dia prem ρ p (snd (ind_pair ρ p n) c) = true ->
      dia Q (n, ρ) (ind_fwd p n) c = true.
  Proof.
    intros ρ p Hρ Hp n; induction n as [| k IH]; intros c Hc Hprem.
    - (* n = 0: the base conjunct at the transported counter *)
      pose proof (proj2 (ind_pair_EEq ρ p Hρ Hp 0) c c Hc) as HCC.
      pose proof (eq_trans
                    (eq_sym (dia_and P0 (pAll (Q ⊃ QS)) ρ ρ p p _ _
                               Hρ Hp HCC)) Hprem) as Hconj.
      apply andb_true_iff in Hconj; destruct Hconj as [Hz _].
      pose proof (eq_trans
                    (eq_sym (dia_psub1 Q tzero ρ ρ (fst p) (fst p) _ _
                               Hρ (proj1 Hp) (proj1 HCC))) Hz) as H0.
      change (dia Q (0, ρ) (tyden_cast eW0 (fst p))
                (tyden_cast eC0 (tyden_cast (eq_sym eC0) c)) = true) in H0.
      rewrite tyden_cast_cancel_sym in H0.
      exact H0.
    - (* n = S k: case on the internal test *)
      change (dia prem ρ p
                (if dia Q (k, ρ) (fst (ind_pair ρ p k))
                      (snd (snd p k) (fst (ind_pair ρ p k))
                         (tyden_cast (eq_sym eCS) c))
                 then (tydefault (C P0),
                       (k, (fst (ind_pair ρ p k), tyden_cast (eq_sym eCS) c)))
                 else snd (ind_pair ρ p k)
                        (snd (snd p k) (fst (ind_pair ρ p k))
                           (tyden_cast (eq_sym eCS) c))) = true) in Hprem.
      destruct (dia Q (k, ρ) (fst (ind_pair ρ p k))
                  (snd (snd p k) (fst (ind_pair ρ p k))
                     (tyden_cast (eq_sym eCS) c))) eqn:Htest.
      + (* test true: blame step k *)
        pose proof (conj (tydefault_EEq (C P0))
                      (conj (@eq_refl nat k)
                         (conj (proj1 (ind_pair_EEq ρ p Hρ Hp k))
                               (EEq_cast (eq_sym eCS) _ _ Hc)))) as Hcnt.
        pose proof (eq_trans
                      (eq_sym (dia_and P0 (pAll (Q ⊃ QS)) ρ ρ p p
                                 (tydefault (C P0),
                                  (k, (fst (ind_pair ρ p k),
                                       tyden_cast (eq_sym eCS) c)))
                                 (tydefault (C P0),
                                  (k, (fst (ind_pair ρ p k),
                                       tyden_cast (eq_sym eCS) c)))
                                 Hρ Hp Hcnt)) Hprem) as Hconj.
        apply andb_true_iff in Hconj; destruct Hconj as [_ Hs].
        pose proof (eq_trans
                      (eq_sym (dia_all (Q ⊃ QS) ρ ρ (snd p) (snd p)
                                 (k, (fst (ind_pair ρ p k),
                                      tyden_cast (eq_sym eCS) c))
                                 (k, (fst (ind_pair ρ p k),
                                      tyden_cast (eq_sym eCS) c))
                                 Hρ (proj2 Hp)
                                 (conj eq_refl
                                    (conj (proj1 (ind_pair_EEq ρ p Hρ Hp k))
                                          (EEq_cast _ _ _ Hc))))) Hs) as H1.
        pose proof (eq_trans
                      (eq_sym (dia_imp Q QS (k, ρ) (k, ρ)
                                 (snd p k) (snd p k)
                                 (fst (ind_pair ρ p k),
                                  tyden_cast (eq_sym eCS) c)
                                 (fst (ind_pair ρ p k),
                                  tyden_cast (eq_sym eCS) c)
                                 (conj eq_refl Hρ) (proj2 Hp k k eq_refl)
                                 (conj (proj1 (ind_pair_EEq ρ p Hρ Hp k))
                                       (EEq_cast _ _ _ Hc)))) H1) as H2.
        assert (HB : dia QS (k, ρ)
                       (fst (snd p k) (fst (ind_pair ρ p k)))
                       (tyden_cast (eq_sym eCS) c) = true).
        { exact (eq_trans (eq_sym (f_equal (fun a => implb a _) Htest)) H2). }
        pose proof (eq_trans
                      (eq_sym (dia_psucc Q (k, ρ) (k, ρ)
                                 (fst (snd p k) (fst (ind_pair ρ p k)))
                                 (fst (snd p k) (fst (ind_pair ρ p k)))
                                 (tyden_cast (eq_sym eCS) c)
                                 (tyden_cast (eq_sym eCS) c)
                                 (conj eq_refl Hρ)
                                 (proj1 (proj2 Hp k k eq_refl) _ _
                                    (proj1 (ind_pair_EEq ρ p Hρ Hp k)))
                                 (EEq_cast _ _ _ Hc))) HB) as H3.
        change (dia Q (S k, ρ)
                  (tyden_cast eWS (fst (snd p k) (fst (ind_pair ρ p k))))
                  (tyden_cast eCS (tyden_cast (eq_sym eCS) c)) = true) in H3.
        rewrite tyden_cast_cancel_sym in H3.
        rewrite ind_fwd_pair in H3.
        exact H3.
      + (* test false: the search descended; contradiction with IH *)
        pose proof (IH (snd (snd p k) (fst (ind_pair ρ p k))
                          (tyden_cast (eq_sym eCS) c))
                      (proj2 (proj2 Hp k k eq_refl) _ _
                         (proj1 (ind_pair_EEq ρ p Hρ Hp k)) _ _
                         (EEq_cast _ _ _ Hc))
                      Hprem) as Hk.
        rewrite ind_fwd_pair in Htest.
        rewrite ind_fwd_pair in Hk.
        rewrite Hk in Htest; discriminate.
  Qed.

End IndSem.

(** ** D2 step 5d: bridging [tmden r_ind] to the semantic mirrors *)

Section IndBridge.
  Context {Γ : cxt} (Q : prp (tN :: Γ)).

  Local Notation P0 := (psub1 Q tzero).
  Local Notation QS := (psucc Q).
  Local Notation prem := (P0 ∧ pAll (Q ⊃ QS)).
  Local Notation eW0 := (W_sub (scons tzero) Q).
  Local Notation eC0 := (C_sub (scons tzero) Q).
  Local Notation eWS := (W_sub sub_succ Q).
  Local Notation eCS := (C_sub sub_succ Q).

  (** The forward component denotes [ind_fwd] — a Leibniz equality, since
      only [tmden_tcast] rewrites are involved.  The [m] slot generalizes
      the (unused) bound variable sitting in the recursion environment. *)
  Lemma r_ind_fwd_rec : forall (ρ : cxtden Γ) (p : tyden (W prem)) (m n : nat),
      nat_rect (fun _ => tyden (W Q))
        (tmden ((tcast eW0 (tfst v1)) : tm (tN :: W prem :: Γ) (W Q))
           (m, (p, ρ)))
        (fun k r => tmden ((tcast eWS (tfst (tsnd v3 · v1) · v0))
                             : tm (W Q :: tN :: tN :: W prem :: Γ) (W Q))
                      (r, (k, (m, (p, ρ))))) n
      = ind_fwd Q p n.
  Proof.
    intros ρ p m n; induction n as [| k IH]; cbn [nat_rect].
    - rewrite tmden_tcast; reflexivity.
    - rewrite tmden_tcast, IH; reflexivity.
  Qed.

  Corollary r_ind_fwd_den : forall (ρ : cxtden Γ) (p : tyden (W prem)) (n : nat),
      fst (tmden (r_ind (Q := Q)) ρ) p n = ind_fwd Q p n.
  Proof.
    intros ρ p n.
    exact (r_ind_fwd_rec ρ p n n).
  Qed.

  (** The backward component denotes [ind_pair] — an [EEq] statement (the
      dummy moves and the internal matrix test only match up to the PER). *)
  Lemma r_ind_bwd_rec : forall (ρ : cxtden Γ) (p : tyden (W prem))
                               (nc : tyden (C (pAll Q))),
      EEqE Γ ρ ρ -> EEq (W prem) p p -> EEq (C (pAll Q)) nc nc ->
      forall n,
        EEq (W Q × (C Q ⇒ C prem))
          (nat_rect (fun _ => tyden (W Q × (C Q ⇒ C prem)))
             (tmden ((tpair (tcast eW0 (tfst v1))
                       (tlam (tpair (tcast (eq_sym eC0) v0)
                                (tpair tzero
                                   (tpair (tdefault (W Q))
                                      (tdefault (C QS)))))))
                       : tm (C (pAll Q) :: W prem :: Γ)
                            (W Q × (C Q ⇒ C prem)))
                (nc, (p, ρ)))
             (fun k h =>
                tmden ((tlam (tlam (tpair
                          (tcast eWS (tfst (tsnd v3 · v1) · tfst v0))
                          (tlam
                             (tif (subst (sub_at0 (drop_prefix [_; _; _; _; _]) v2) (diaT Q) · tfst v1
                                     · (tsnd (tsnd v4 · v2) · tfst v1
                                          · tcast (eq_sym eCS) v0))
                                (tpair (tdefault (C P0))
                                   (tpair v2
                                      (tpair (tfst v1)
                                         (tcast (eq_sym eCS) v0))))
                                (tsnd v1 · (tsnd (tsnd v4 · v2) · tfst v1
                                              · tcast (eq_sym eCS) v0)))))))
                          : tm (C (pAll Q) :: W prem :: Γ)
                               (tN ⇒ (W Q × (C Q ⇒ C prem))
                                   ⇒ (W Q × (C Q ⇒ C prem))))
                   (nc, (p, ρ)) k h) n)
          (ind_pair Q ρ p n).
  Proof.
    intros ρ p nc Hρ Hp Hnc n; induction n as [| k IH]; cbn [nat_rect].
    - (* base *)
      split.
      + assert (H1 : EEq (W Q)
            (tmden ((tcast eW0 (tfst v1))
                      : tm (C (pAll Q) :: W prem :: Γ) (W Q)) (nc, (p, ρ)))
            (tyden_cast eW0 (fst p))).
        { rewrite tmden_tcast; exact (EEq_cast _ _ _ (proj1 Hp)). }
        exact H1.
      + intros c c' Hc.
        split.
        * assert (H1 : EEq (C P0)
              (tmden ((tcast (eq_sym eC0) v0)
                        : tm (C Q :: C (pAll Q) :: W prem :: Γ) (C P0))
                 (c, (nc, (p, ρ))))
              (tyden_cast (eq_sym eC0) c')).
          { rewrite tmden_tcast; exact (EEq_cast _ _ _ Hc). }
          exact H1.
        * split; [reflexivity |].
          split;
            [ exact (tmden_tdefault (W Q)
                       (Γ := C Q :: C (pAll Q) :: W prem :: Γ)
                       (c, (nc, (p, ρ))))
            | exact (tmden_tdefault (C QS)
                       (Γ := C Q :: C (pAll Q) :: W prem :: Γ)
                       (c, (nc, (p, ρ)))) ].
    - (* step: abstract the recursor value *)
      revert IH.
      match goal with
      | |- context [nat_rect ?A ?z ?f k] => generalize (nat_rect A z f k)
      end; intros h IH.
      pose proof (EEq_refl_l _ _ _ IH) as Hh.
      split.
      + assert (H1 : EEq (W Q)
            (tmden ((tcast eWS (tfst (tsnd v3 · v1) · tfst v0))
                      : tm ((W Q × (C Q ⇒ C prem)) :: tN
                            :: C (pAll Q) :: W prem :: Γ) (W Q))
               (h, (k, (nc, (p, ρ)))))
            (tyden_cast eWS (fst (snd p k) (fst (ind_pair Q ρ p k))))).
        { rewrite tmden_tcast.
          exact (EEq_cast _ _ _
                   (proj1 (proj2 Hp k k eq_refl) _ _ (proj1 IH))). }
        exact H1.
      + intros c c' Hc.
        pose proof (conj (EEq_refl_l _ _ _ Hc)
                      (conj Hh (conj (@eq_refl nat k)
                         (conj Hnc (conj Hp Hρ))))) as Eself.
        assert (HcSden : EEq (C QS)
            (tmden ((tcast (eq_sym eCS) v0)
                      : tm (C Q :: (W Q × (C Q ⇒ C prem)) :: tN
                            :: C (pAll Q) :: W prem :: Γ) (C QS))
               (c, (h, (k, (nc, (p, ρ))))))
            (tyden_cast (eq_sym eCS) c')).
        { rewrite tmden_tcast; exact (EEq_cast _ _ _ Hc). }
        assert (Hcden : EEq (C Q)
            (snd (snd p k) (fst h)
               (tmden ((tcast (eq_sym eCS) v0)
                         : tm (C Q :: (W Q × (C Q ⇒ C prem)) :: tN
                               :: C (pAll Q) :: W prem :: Γ) (C QS))
                  (c, (h, (k, (nc, (p, ρ)))))))
            (snd (snd p k) (fst (ind_pair Q ρ p k))
               (tyden_cast (eq_sym eCS) c'))).
        { exact (proj2 (proj2 Hp k k eq_refl) _ _ (proj1 IH) _ _ HcSden). }
        assert (Hdia : EEq (W Q ⇒ C Q ⇒ tBool)
            (tmden ((subst (sub_at0 (drop_prefix [_; _; _; _; _]) v2) (diaT Q))
                      : tm (C Q :: (W Q × (C Q ⇒ C prem)) :: tN
                            :: C (pAll Q) :: W prem :: Γ)
                           (W Q ⇒ C Q ⇒ tBool))
               (c, (h, (k, (nc, (p, ρ))))))
            (tmden (diaT Q) (k, ρ))).
        { apply EEq_trans with
            (b := tmden (diaT Q)
                    (subden (sub_at0 (drop_prefix [_; _; _; _; _]) v2) (c, (h, (k, (nc, (p, ρ))))))).
          - exact (tmden_subst (diaT Q) (sub_at0 (drop_prefix [_; _; _; _; _]) v2)
                     (c, (h, (k, (nc, (p, ρ)))))
                     (c, (h, (k, (nc, (p, ρ))))) Eself).
          - apply tmden_EEqE.
            pose proof (subden_sub_at0 (drop_prefix [_; _; _; _; _]) v2
                          (c, (h, (k, (nc, (p, ρ)))))
                          (c, (h, (k, (nc, (p, ρ))))) Eself) as H2.
            rewrite opeden_drop_prefix in H2; exact H2. }
        assert (Hcond : tmden ((subst (sub_at0 (drop_prefix [_; _; _; _; _]) v2) (diaT Q))
                                 : tm (C Q :: (W Q × (C Q ⇒ C prem)) :: tN
                                       :: C (pAll Q) :: W prem :: Γ)
                                      (W Q ⇒ C Q ⇒ tBool))
                          (c, (h, (k, (nc, (p, ρ)))))
                          (fst h)
                          (snd (snd p k) (fst h)
                             (tmden ((tcast (eq_sym eCS) v0)
                                       : tm (C Q :: (W Q × (C Q ⇒ C prem))
                                             :: tN :: C (pAll Q)
                                             :: W prem :: Γ) (C QS))
                                (c, (h, (k, (nc, (p, ρ)))))))
                        = dia Q (k, ρ) (fst (ind_pair Q ρ p k))
                            (snd (snd p k) (fst (ind_pair Q ρ p k))
                               (tyden_cast (eq_sym eCS) c'))).
        { exact (Hdia _ _ (proj1 IH) _ _ Hcden). }
        assert (HH : EEq (C prem)
            (if tmden ((subst (sub_at0 (drop_prefix [_; _; _; _; _]) v2) (diaT Q))
                         : tm (C Q :: (W Q × (C Q ⇒ C prem)) :: tN
                               :: C (pAll Q) :: W prem :: Γ)
                              (W Q ⇒ C Q ⇒ tBool))
                  (c, (h, (k, (nc, (p, ρ)))))
                  (fst h)
                  (snd (snd p k) (fst h)
                     (tmden ((tcast (eq_sym eCS) v0)
                               : tm (C Q :: (W Q × (C Q ⇒ C prem)) :: tN
                                     :: C (pAll Q) :: W prem :: Γ) (C QS))
                        (c, (h, (k, (nc, (p, ρ)))))))
             then (tmden ((tdefault (C P0))
                            : tm (C Q :: (W Q × (C Q ⇒ C prem)) :: tN
                                  :: C (pAll Q) :: W prem :: Γ) (C P0))
                     (c, (h, (k, (nc, (p, ρ))))),
                   (k, (fst h,
                        tmden ((tcast (eq_sym eCS) v0)
                                 : tm (C Q :: (W Q × (C Q ⇒ C prem)) :: tN
                                       :: C (pAll Q) :: W prem :: Γ) (C QS))
                          (c, (h, (k, (nc, (p, ρ))))))))
             else snd h
                    (snd (snd p k) (fst h)
                       (tmden ((tcast (eq_sym eCS) v0)
                                 : tm (C Q :: (W Q × (C Q ⇒ C prem)) :: tN
                                       :: C (pAll Q) :: W prem :: Γ) (C QS))
                          (c, (h, (k, (nc, (p, ρ))))))))
            (if dia Q (k, ρ) (fst (ind_pair Q ρ p k))
                  (snd (snd p k) (fst (ind_pair Q ρ p k))
                     (tyden_cast (eq_sym eCS) c'))
             then (tydefault (C P0),
                   (k, (fst (ind_pair Q ρ p k), tyden_cast (eq_sym eCS) c')))
             else snd (ind_pair Q ρ p k)
                    (snd (snd p k) (fst (ind_pair Q ρ p k))
                       (tyden_cast (eq_sym eCS) c')))).
        { rewrite Hcond.
          destruct (dia Q (k, ρ) (fst (ind_pair Q ρ p k))
                      (snd (snd p k) (fst (ind_pair Q ρ p k))
                         (tyden_cast (eq_sym eCS) c'))).
          - split;
              [ exact (tmden_tdefault (C P0)
                         (Γ := C Q :: (W Q × (C Q ⇒ C prem)) :: tN
                               :: C (pAll Q) :: W prem :: Γ)
                         (c, (h, (k, (nc, (p, ρ)))))) |].
            split; [reflexivity |].
            split; [exact (proj1 IH) | exact HcSden].
          - exact (proj2 IH _ _ Hcden). }
        exact HH.
  Qed.

End IndBridge.

(** The backward component, in the applied form [Valid_r_ind] consumes. *)
Lemma r_ind_bwd_den : forall {Γ} (Q : prp (tN :: Γ)) (ρ : cxtden Γ)
                             (p : tyden (W (psub1 Q tzero ∧ pAll (Q ⊃ psucc Q))))
                             (nc : tyden (C (pAll Q))),
    EEqE Γ ρ ρ ->
    EEq (W (psub1 Q tzero ∧ pAll (Q ⊃ psucc Q))) p p ->
    EEq (C (pAll Q)) nc nc ->
    EEq (C (psub1 Q tzero ∧ pAll (Q ⊃ psucc Q)))
        (snd (tmden (r_ind (Q := Q)) ρ) p nc)
        (snd (ind_pair Q ρ p (fst nc)) (snd nc)).
Proof.
  intros Γ Q ρ p nc Hρ Hp Hnc.
  exact (proj2 (r_ind_bwd_rec Q ρ p nc Hρ Hp Hnc (fst nc)) (snd nc) (snd nc)
           (proj2 Hnc)).
Qed.

(** Validity of the induction realizer — steps 5a–5d assembled: unfold the
    implication and the universal, transport the premise along the backward
    bridge, conclude with the search spec and the forward bridge. *)
Lemma Valid_r_ind : forall {Γ} (Q : prp (tN :: Γ)),
    valid ((psub1 Q tzero ∧ pAll (Q ⊃ psucc Q)) ⊃ pAll Q) (r_ind (Q := Q)).
Proof.
  intros Γ Q ρ cc Hρ Hcc.
  pose proof (tmden_EEqE (r_ind (Q := Q)) ρ ρ Hρ) as Hr.
  pose proof (dia_imp (psub1 Q tzero ∧ pAll (Q ⊃ psucc Q)) (pAll Q) ρ ρ
                (tmden (r_ind (Q := Q)) ρ) (tmden (r_ind (Q := Q)) ρ)
                cc cc Hρ Hr Hcc) as E.
  refine (eq_trans E _).
  destruct (dia (psub1 Q tzero ∧ pAll (Q ⊃ psucc Q)) ρ (fst cc)
              (snd (tmden (r_ind (Q := Q)) ρ) (fst cc) (snd cc))) eqn:Hprem.
  - (* premise holds: conclude through the search *)
    assert (Hprem' : dia (psub1 Q tzero ∧ pAll (Q ⊃ psucc Q)) ρ (fst cc)
                       (snd (ind_pair Q ρ (fst cc) (fst (snd cc)))
                          (snd (snd cc))) = true).
    { exact (eq_trans
               (eq_sym (dia_EEqE (psub1 Q tzero ∧ pAll (Q ⊃ psucc Q)) ρ ρ
                          (fst cc) (fst cc) _ _
                          Hρ (proj1 Hcc)
                          (r_ind_bwd_den Q ρ (fst cc) (snd cc)
                             Hρ (proj1 Hcc) (proj2 Hcc)))) Hprem). }
    pose proof (ind_spec Q ρ (fst cc) Hρ (proj1 Hcc) (fst (snd cc))
                  (snd (snd cc)) (proj2 (proj2 Hcc)) Hprem') as Hgoal.
    pose proof (dia_all Q ρ ρ
                  (fst (tmden (r_ind (Q := Q)) ρ) (fst cc))
                  (fst (tmden (r_ind (Q := Q)) ρ) (fst cc))
                  (snd cc) (snd cc) Hρ
                  (proj1 Hr _ _ (proj1 Hcc)) (proj2 Hcc)) as E3.
    refine (eq_trans E3 _).
    refine (eq_trans (f_equal (fun w => dia Q (fst (snd cc), ρ) w
                                          (snd (snd cc)))
                        (r_ind_fwd_den Q ρ (fst cc) (fst (snd cc)))) _).
    exact Hgoal.
  - (* premise fails: the implication is vacuous *)
    reflexivity.
Qed.

(** ** D2 step 6: validity of the realizer combinators

    One lemma per combinator, in the combinator-plus-lemma style of
    theories_old/linear.v; rules with premises get conditional lemmas.
    All arguments are conducted against the [dia_*] characterization —
    [diaT] is never unfolded. *)

Lemma Valid_tunit_true : forall {Γ}, valid (@pTrue Γ) tunit.
Proof.
  intros Γ ρ c Hρ _.
  exact (dia_atom ttrue ρ ρ (tmden tunit ρ) c Hρ).
Qed.

Lemma Valid_teqb_refl : forall {Γ} (t : tm Γ tN), valid (pEq t t) tunit.
Proof.
  intros Γ t ρ c Hρ _.
  refine (eq_trans (dia_atom (teqb · t · t) ρ ρ (tmden tunit ρ) c Hρ) _).
  exact (teqb_refl ρ (tmden t ρ)).
Qed.

(** Any semantically valid implication between atoms is realized by the
    administrative pair (covers the successor axioms). *)
Lemma Valid_r_atom_imp : forall {Γ} (b b' : tm Γ tBool),
    (forall ρ, EEqE Γ ρ ρ -> tmden b ρ = true -> tmden b' ρ = true) ->
    valid (pAtom b ⊃ pAtom b') (r_atom_imp (b := b) (b' := b')).
Proof.
  intros Γ b b' Himp ρ cc Hρ Hcc.
  refine (eq_trans (dia_imp (pAtom b) (pAtom b') ρ ρ _ _ cc cc Hρ
            (tmden_EEqE (r_atom_imp (b := b) (b' := b')) ρ ρ Hρ) Hcc) _).
  destruct (dia (pAtom b) ρ (fst cc)
              (snd (tmden (r_atom_imp (b := b) (b' := b')) ρ) (fst cc) (snd cc)))
    eqn:HA; [| reflexivity].
  refine (eq_trans (dia_atom b' ρ ρ _ _ Hρ) _).
  apply (Himp ρ Hρ).
  exact (eq_trans (eq_sym (dia_atom b ρ ρ (fst cc)
           (snd (tmden (r_atom_imp (b := b) (b' := b')) ρ) (fst cc) (snd cc))
           Hρ)) HA).
Qed.

Lemma Valid_succ_nonzero : forall {Γ} (t : tm Γ tN),
    valid (pNot (pEq (tsuc t) tzero))
          (r_atom_imp (b := teqb · tsuc t · tzero) (b' := tfalse)).
Proof.
  intros Γ t.
  apply Valid_r_atom_imp.
  intros ρ _ H.
  exfalso.
  pose proof (eq_trans (eq_sym (teqb_spec ρ (S (tmden t ρ)) 0)) H) as H'.
  discriminate H'.
Qed.

Lemma Valid_succ_inj : forall {Γ} (t s : tm Γ tN),
    valid (pEq (tsuc t) (tsuc s) ⊃ pEq t s)
          (r_atom_imp (b := teqb · tsuc t · tsuc s) (b' := teqb · t · s)).
Proof.
  intros Γ t s.
  apply Valid_r_atom_imp.
  intros ρ _ H.
  pose proof (eq_trans (eq_sym (teqb_spec ρ (S (tmden t ρ)) (S (tmden s ρ))))
                H) as H'.
  exact (eq_trans (teqb_spec ρ (tmden t ρ) (tmden s ρ)) H').
Qed.

Lemma Valid_r_mp : forall {Γ} {P Q : prp Γ}
    (u : tm Γ (W (P ⊃ Q))) (a : tm Γ (W P)),
    valid (P ⊃ Q) u -> valid P a -> valid Q (r_mp u a).
Proof.
  intros Γ P Q u a Hu Ha ρ c Hρ Hc.
  pose proof (tmden_EEqE u ρ ρ Hρ) as HuD.
  pose proof (tmden_EEqE a ρ ρ Hρ) as HaD.
  pose proof (Hu ρ (tmden a ρ, c) Hρ (conj HaD Hc)) as HU.
  pose proof (eq_trans (eq_sym (dia_imp P Q ρ ρ (tmden u ρ) (tmden u ρ)
                (tmden a ρ, c) (tmden a ρ, c) Hρ HuD (conj HaD Hc))) HU) as HU'.
  pose proof (Ha ρ (snd (tmden u ρ) (tmden a ρ) c) Hρ
                (proj2 HuD _ _ HaD _ _ Hc)) as HA.
  exact (implb_true_elim _ _ HU' HA).
Qed.

Lemma Valid_r_and_comm : forall {Γ} {P Q : prp Γ},
    valid (P ∧ Q ⊃ Q ∧ P) (r_and_comm (P := P) (Q := Q)).
Proof.
  intros Γ P Q ρ cc Hρ Hcc.
  pose proof (proj1 Hcc) as Hw; pose proof (proj2 Hcc) as Hc.
  refine (eq_trans (dia_imp (P ∧ Q) (Q ∧ P) ρ ρ _ _ cc cc Hρ
            (tmden_EEqE (r_and_comm (P := P) (Q := Q)) ρ ρ Hρ) Hcc) _).
  destruct (dia (P ∧ Q) ρ (fst cc)
              (snd (tmden (r_and_comm (P := P) (Q := Q)) ρ) (fst cc) (snd cc)))
    eqn:HA; [| reflexivity].
  pose proof (eq_trans (eq_sym (dia_and P Q ρ ρ (fst cc) (fst cc)
                (snd (snd cc), fst (snd cc)) (snd (snd cc), fst (snd cc))
                Hρ Hw (conj (proj2 Hc) (proj1 Hc)))) HA) as H1.
  apply andb_true_iff in H1; destruct H1 as [HP HQ].
  cbn [fst snd] in HP, HQ.
  refine (eq_trans (dia_and Q P ρ ρ
            (fst (tmden (r_and_comm (P := P) (Q := Q)) ρ) (fst cc))
            (snd (fst cc), fst (fst cc)) (snd cc) (snd cc) Hρ
            (conj (proj2 Hw) (proj1 Hw)) Hc) _).
  cbn [fst snd].
  rewrite HQ, HP; reflexivity.
Qed.

Lemma Valid_r_or_comm : forall {Γ} {P Q : prp Γ},
    valid (P ∨ Q ⊃ Q ∨ P) (r_or_comm (P := P) (Q := Q)).
Proof.
  intros Γ P Q ρ cc Hρ Hcc.
  pose proof (proj1 Hcc) as Hw; pose proof (proj2 Hcc) as Hc.
  refine (eq_trans (dia_imp (P ∨ Q) (Q ∨ P) ρ ρ _ _ cc cc Hρ
            (tmden_EEqE (r_or_comm (P := P) (Q := Q)) ρ ρ Hρ) Hcc) _).
  destruct (dia (P ∨ Q) ρ (fst cc)
              (snd (tmden (r_or_comm (P := P) (Q := Q)) ρ) (fst cc) (snd cc)))
    eqn:HA; [| reflexivity].
  pose proof (eq_trans (eq_sym (dia_or P Q ρ ρ (fst cc) (fst cc)
                (snd (snd cc), fst (snd cc)) (snd (snd cc), fst (snd cc))
                Hρ Hw (conj (proj2 Hc) (proj1 Hc)))) HA) as H1.
  cbn [fst snd] in H1.
  refine (eq_trans (dia_or Q P ρ ρ
            (fst (tmden (r_or_comm (P := P) (Q := Q)) ρ) (fst cc))
            (negb (fst (fst cc)), (snd (snd (fst cc)), fst (snd (fst cc))))
            (snd cc) (snd cc) Hρ
            (conj eq_refl (conj (proj2 (proj2 Hw)) (proj1 (proj2 Hw)))) Hc) _).
  cbn [fst snd].
  destruct (fst (fst cc)) eqn:Hflag; try rewrite Hflag in H1; exact H1.
Qed.

Lemma Valid_r_or_contr : forall {Γ} {P : prp Γ},
    valid (P ∨ P ⊃ P) (r_or_contr (P := P)).
Proof.
  intros Γ P ρ cc Hρ Hcc.
  pose proof (proj1 Hcc) as Hw; pose proof (proj2 Hcc) as Hc.
  refine (eq_trans (dia_imp (P ∨ P) P ρ ρ _ _ cc cc Hρ
            (tmden_EEqE (r_or_contr (P := P)) ρ ρ Hρ) Hcc) _).
  destruct (dia (P ∨ P) ρ (fst cc)
              (snd (tmden (r_or_contr (P := P)) ρ) (fst cc) (snd cc)))
    eqn:HA; [| reflexivity].
  pose proof (eq_trans (eq_sym (dia_or P P ρ ρ (fst cc) (fst cc)
                (snd cc, snd cc) (snd cc, snd cc)
                Hρ Hw (conj Hc Hc))) HA) as H1.
  cbn [fst snd] in H1.
  destruct (fst (fst cc)) eqn:Hflag; try rewrite Hflag in H1;
    exact (eq_trans (f_equal (fun b : bool => dia P ρ
             (if b then fst (snd (fst cc)) else snd (snd (fst cc)))
             (snd cc)) Hflag) H1).
Qed.

Lemma Valid_r_and_eliml : forall {Γ} {P Q : prp Γ},
    valid (P ∧ Q ⊃ P) (r_and_eliml (P := P) (Q := Q)).
Proof.
  intros Γ P Q ρ cc Hρ Hcc.
  pose proof (proj1 Hcc) as Hw; pose proof (proj2 Hcc) as Hc.
  refine (eq_trans (dia_imp (P ∧ Q) P ρ ρ _ _ cc cc Hρ
            (tmden_EEqE (r_and_eliml (P := P) (Q := Q)) ρ ρ Hρ) Hcc) _).
  destruct (dia (P ∧ Q) ρ (fst cc)
              (snd (tmden (r_and_eliml (P := P) (Q := Q)) ρ) (fst cc) (snd cc)))
    eqn:HA; [| reflexivity].
  pose proof (eq_trans (eq_sym (dia_and P Q ρ ρ (fst cc) (fst cc)
                (snd (tmden (r_and_eliml (P := P) (Q := Q)) ρ) (fst cc) (snd cc))
                (snd (tmden (r_and_eliml (P := P) (Q := Q)) ρ) (fst cc) (snd cc))
                Hρ Hw
                (proj2 (tmden_EEqE (r_and_eliml (P := P) (Q := Q)) ρ ρ Hρ)
                   _ _ Hw _ _ Hc))) HA) as H1.
  apply andb_true_iff in H1; destruct H1 as [H1 _].
  exact H1.
Qed.

Lemma Valid_r_or_inl : forall {Γ} {P Q : prp Γ},
    valid (P ⊃ P ∨ Q) (r_or_inl (P := P) (Q := Q)).
Proof.
  intros Γ P Q ρ cc Hρ Hcc.
  pose proof (proj1 Hcc) as Hw; pose proof (proj2 Hcc) as Hc.
  refine (eq_trans (dia_imp P (P ∨ Q) ρ ρ _ _ cc cc Hρ
            (tmden_EEqE (r_or_inl (P := P) (Q := Q)) ρ ρ Hρ) Hcc) _).
  destruct (dia P ρ (fst cc)
              (snd (tmden (r_or_inl (P := P) (Q := Q)) ρ) (fst cc) (snd cc)))
    eqn:HA; [| reflexivity].
  refine (eq_trans (dia_or P Q ρ ρ
            (fst (tmden (r_or_inl (P := P) (Q := Q)) ρ) (fst cc))
            (fst (tmden (r_or_inl (P := P) (Q := Q)) ρ) (fst cc))
            (snd cc) (snd cc) Hρ
            (proj1 (tmden_EEqE (r_or_inl (P := P) (Q := Q)) ρ ρ Hρ) _ _ Hw)
            Hc) _).
  exact HA.
Qed.

Lemma Valid_r_exfalso : forall {Γ} {P : prp Γ},
    valid (pFalse ⊃ P) (r_exfalso (P := P)).
Proof.
  intros Γ P ρ cc Hρ Hcc.
  refine (eq_trans (dia_imp pFalse P ρ ρ _ _ cc cc Hρ
            (tmden_EEqE (r_exfalso (P := P)) ρ ρ Hρ) Hcc) _).
  destruct (dia pFalse ρ (fst cc)
              (snd (tmden (r_exfalso (P := P)) ρ) (fst cc) (snd cc)))
    eqn:HA; [| reflexivity].
  exfalso.
  pose proof (eq_trans (eq_sym (dia_atom tfalse ρ ρ (fst cc)
                (snd (tmden (r_exfalso (P := P)) ρ) (fst cc) (snd cc)) Hρ)) HA)
    as H1.
  discriminate H1.
Qed.

Lemma Valid_r_chain : forall {Γ} {P Q R : prp Γ}
    (u : tm Γ (W (P ⊃ Q))) (v : tm Γ (W (Q ⊃ R))),
    valid (P ⊃ Q) u -> valid (Q ⊃ R) v -> valid (P ⊃ R) (r_chain u v).
Proof.
  intros Γ P Q R u v Hu Hv ρ cc Hρ Hcc.
  pose proof (proj1 Hcc) as Hw; pose proof (proj2 Hcc) as Hc.
  pose proof (tmden_EEqE u ρ ρ Hρ) as HuD.
  pose proof (tmden_EEqE v ρ ρ Hρ) as HvD.
  refine (eq_trans (dia_imp P R ρ ρ _ _ cc cc Hρ
            (tmden_EEqE (r_chain u v) ρ ρ Hρ) Hcc) _).
  destruct (dia P ρ (fst cc)
              (snd (tmden (r_chain u v) ρ) (fst cc) (snd cc))) eqn:HA;
    [| reflexivity].
  pose proof (tmden_wk1_EEq (S := W P) u (fst cc) (fst cc) ρ ρ Hw Hρ) as Bu1.
  pose proof (tmden_wk1_EEq (S := W P) v (fst cc) (fst cc) ρ ρ Hw Hρ) as Bv1.
  pose proof (tmden_wk2_EEq (S1 := C R) (S2 := W P) u
                (snd cc) (snd cc) (fst cc) (fst cc) ρ ρ Hc Hw Hρ) as Bu2.
  pose proof (tmden_wk2_EEq (S1 := C R) (S2 := W P) v
                (snd cc) (snd cc) (fst cc) (fst cc) ρ ρ Hc Hw Hρ) as Bv2.
  assert (Hcnt : EEq (C P)
      (snd (tmden (wk1 (S := C R) (wk1 (S := W P) u)) (snd cc, (fst cc, ρ)))
         (fst cc)
         (snd (tmden (wk1 (S := C R) (wk1 (S := W P) v))
                 (snd cc, (fst cc, ρ)))
            (fst (tmden (wk1 (S := C R) (wk1 (S := W P) u))
                    (snd cc, (fst cc, ρ))) (fst cc))
            (snd cc)))
      (snd (tmden u ρ) (fst cc)
         (snd (tmden v ρ) (fst (tmden u ρ) (fst cc)) (snd cc)))).
  { exact (proj2 Bu2 _ _ Hw _ _
             (proj2 Bv2 _ _ (proj1 Bu2 _ _ Hw) _ _ Hc)). }
  assert (HP : dia P ρ (fst cc)
                 (snd (tmden u ρ) (fst cc)
                    (snd (tmden v ρ) (fst (tmden u ρ) (fst cc)) (snd cc)))
               = true).
  { exact (eq_trans (eq_sym (dia_EEqE P ρ ρ (fst cc) (fst cc) _ _
                       Hρ Hw Hcnt)) HA). }
  pose proof (Hu ρ (fst cc,
                    snd (tmden v ρ) (fst (tmden u ρ) (fst cc)) (snd cc)) Hρ
                (conj Hw (proj2 HvD _ _ (proj1 HuD _ _ Hw) _ _ Hc))) as HU.
  pose proof (eq_trans (eq_sym (dia_imp P Q ρ ρ (tmden u ρ) (tmden u ρ)
                (fst cc, snd (tmden v ρ) (fst (tmden u ρ) (fst cc)) (snd cc))
                (fst cc, snd (tmden v ρ) (fst (tmden u ρ) (fst cc)) (snd cc))
                Hρ HuD
                (conj Hw (proj2 HvD _ _ (proj1 HuD _ _ Hw) _ _ Hc)))) HU)
    as HU'.
  pose proof (implb_true_elim _ _ HU' HP) as HQ.
  pose proof (Hv ρ (fst (tmden u ρ) (fst cc), snd cc) Hρ
                (conj (proj1 HuD _ _ Hw) Hc)) as HV.
  pose proof (eq_trans (eq_sym (dia_imp Q R ρ ρ (tmden v ρ) (tmden v ρ)
                (fst (tmden u ρ) (fst cc), snd cc)
                (fst (tmden u ρ) (fst cc), snd cc)
                Hρ HvD (conj (proj1 HuD _ _ Hw) Hc))) HV) as HV'.
  pose proof (implb_true_elim _ _ HV' HQ) as HR.
  assert (Hfw : EEq (W R)
      (fst (tmden (wk1 (S := W P) v) (fst cc, ρ))
         (fst (tmden (wk1 (S := W P) u) (fst cc, ρ)) (fst cc)))
      (fst (tmden v ρ) (fst (tmden u ρ) (fst cc)))).
  { exact (proj1 Bv1 _ _ (proj1 Bu1 _ _ Hw)). }
  exact (eq_trans (dia_EEqE R ρ ρ _ _ (snd cc) (snd cc) Hρ Hfw Hc) HR).
Qed.

Lemma Valid_r_or_distr : forall {Γ} {P Q R : prp Γ} (u : tm Γ (W (P ⊃ Q))),
    valid (P ⊃ Q) u -> valid (R ∨ P ⊃ R ∨ Q) (r_or_distr (R := R) u).
Proof.
  intros Γ P Q R u Hu ρ cc Hρ Hcc.
  pose proof (proj1 Hcc) as Hw; pose proof (proj2 Hcc) as Hc.
  pose proof (tmden_EEqE u ρ ρ Hρ) as HuD.
  refine (eq_trans (dia_imp (R ∨ P) (R ∨ Q) ρ ρ _ _ cc cc Hρ
            (tmden_EEqE (r_or_distr (R := R) u) ρ ρ Hρ) Hcc) _).
  destruct (dia (R ∨ P) ρ (fst cc)
              (snd (tmden (r_or_distr (R := R) u) ρ) (fst cc) (snd cc)))
    eqn:HA; [| reflexivity].
  pose proof (tmden_wk1_EEq (S := W (R ∨ P)) u (fst cc) (fst cc) ρ ρ Hw Hρ)
    as Bu1.
  pose proof (tmden_wk2_EEq (S1 := C (R ∨ Q)) (S2 := W (R ∨ P)) u
                (snd cc) (snd cc) (fst cc) (fst cc) ρ ρ Hc Hw Hρ) as Bu2.
  pose proof (conj (proj1 Hc)
                (proj2 Bu2 _ _ (proj2 (proj2 Hw)) _ _ (proj2 Hc))
              : EEq (C (R ∨ P))
                  (fst (snd cc),
                   snd (tmden (wk1 (S := C (R ∨ Q)) (wk1 (S := W (R ∨ P)) u))
                          (snd cc, (fst cc, ρ)))
                     (snd (snd (fst cc))) (snd (snd cc)))
                  (fst (snd cc),
                   snd (tmden u ρ) (snd (snd (fst cc))) (snd (snd cc))))
    as Hcnt.
  assert (HP : dia (R ∨ P) ρ (fst cc)
                 (fst (snd cc),
                  snd (tmden u ρ) (snd (snd (fst cc))) (snd (snd cc)))
               = true).
  { exact (eq_trans (eq_sym (dia_EEqE (R ∨ P) ρ ρ (fst cc) (fst cc) _ _
                       Hρ Hw Hcnt)) HA). }
  pose proof (eq_trans (eq_sym (dia_or R P ρ ρ (fst cc) (fst cc)
                (fst (snd cc),
                 snd (tmden u ρ) (snd (snd (fst cc))) (snd (snd cc)))
                (fst (snd cc),
                 snd (tmden u ρ) (snd (snd (fst cc))) (snd (snd cc)))
                Hρ Hw
                (conj (proj1 Hc)
                   (proj2 HuD _ _ (proj2 (proj2 Hw)) _ _ (proj2 Hc)))))
                HP) as H1.
  cbn [fst snd] in H1.
  refine (eq_trans (dia_or R Q ρ ρ
            (fst (tmden (r_or_distr (R := R) u) ρ) (fst cc))
            (fst (fst cc),
             (fst (snd (fst cc)),
              fst (tmden u ρ) (snd (snd (fst cc)))))
            (snd cc) (snd cc) Hρ
            (conj eq_refl
               (conj (proj1 (proj2 Hw))
                  (proj1 Bu1 _ _ (proj2 (proj2 Hw))))) Hc) _).
  cbn [fst snd].
  destruct (fst (fst cc)) eqn:Hflag; try rewrite Hflag in H1.
  - exact H1.
  - pose proof (Hu ρ (snd (snd (fst cc)), snd (snd cc)) Hρ
                  (conj (proj2 (proj2 Hw)) (proj2 Hc))) as HU.
    pose proof (eq_trans (eq_sym (dia_imp P Q ρ ρ (tmden u ρ) (tmden u ρ)
                  (snd (snd (fst cc)), snd (snd cc))
                  (snd (snd (fst cc)), snd (snd cc))
                  Hρ HuD (conj (proj2 (proj2 Hw)) (proj2 Hc)))) HU) as HU'.
    exact (implb_true_elim _ _ HU' H1).
Qed.

Lemma Valid_r_cur : forall {Γ} {P Q R : prp Γ} (u : tm Γ (W (P ∧ Q ⊃ R))),
    valid (P ∧ Q ⊃ R) u -> valid (P ⊃ (Q ⊃ R)) (r_cur u).
Proof.
  intros Γ P Q R u Hu ρ cc Hρ Hcc.
  pose proof (proj1 Hcc) as Hw; pose proof (proj2 Hcc) as Hc.
  pose proof (tmden_EEqE u ρ ρ Hρ) as HuD.
  refine (eq_trans (dia_imp P (Q ⊃ R) ρ ρ _ _ cc cc Hρ
            (tmden_EEqE (r_cur u) ρ ρ Hρ) Hcc) _).
  destruct (dia P ρ (fst cc)
              (snd (tmden (r_cur u) ρ) (fst cc) (snd cc))) eqn:HA;
    [| reflexivity].
  pose proof (tmden_wk2_EEq (S1 := C (Q ⊃ R)) (S2 := W P) u
                (snd cc) (snd cc) (fst cc) (fst cc) ρ ρ Hc Hw Hρ) as Buqc.
  pose proof (tmden_wk2_EEq (S1 := W Q) (S2 := W P) u
                (fst (snd cc)) (fst (snd cc)) (fst cc) (fst cc)
                ρ ρ (proj1 Hc) Hw Hρ) as Buq.
  pose proof (EEq_trans _ _ _ _
                (tmden_wk1_EEq (S := C R)
                   (wk1 (S := W Q) (wk1 (S := W P) u))
                   (snd (snd cc)) (snd (snd cc))
                   (fst (snd cc), (fst cc, ρ)) (fst (snd cc), (fst cc, ρ))
                   (proj2 Hc) (conj (proj1 Hc) (conj Hw Hρ)))
                Buq) as Bu3.
  assert (HcntP : EEq (C P)
      (fst (snd (tmden (wk1 (S := C (Q ⊃ R)) (wk1 (S := W P) u))
                   (snd cc, (fst cc, ρ)))
              (fst cc, fst (snd cc)) (snd (snd cc))))
      (fst (snd (tmden u ρ) (fst cc, fst (snd cc)) (snd (snd cc))))).
  { exact (proj1 (proj2 Buqc (fst cc, fst (snd cc)) (fst cc, fst (snd cc))
              (conj Hw (proj1 Hc)) _ _ (proj2 Hc))). }
  assert (HP : dia P ρ (fst cc)
                 (fst (snd (tmden u ρ) (fst cc, fst (snd cc)) (snd (snd cc))))
               = true).
  { exact (eq_trans (eq_sym (dia_EEqE P ρ ρ (fst cc) (fst cc) _ _
                       Hρ Hw HcntP)) HA). }
  refine (eq_trans (dia_imp Q R ρ ρ
            (fst (tmden (r_cur u) ρ) (fst cc))
            (fst (tmden (r_cur u) ρ) (fst cc))
            (snd cc) (snd cc) Hρ
            (proj1 (tmden_EEqE (r_cur u) ρ ρ Hρ) _ _ Hw) Hc) _).
  destruct (dia Q ρ (fst (snd cc))
              (snd (fst (tmden (r_cur u) ρ) (fst cc)) (fst (snd cc))
                 (snd (snd cc)))) eqn:HB; [| reflexivity].
  assert (HcntQ : EEq (C Q)
      (snd (snd (tmden (wk1 (S := C R)
                          (wk1 (S := W Q) (wk1 (S := W P) u)))
                   (snd (snd cc), (fst (snd cc), (fst cc, ρ))))
              (fst cc, fst (snd cc)) (snd (snd cc))))
      (snd (snd (tmden u ρ) (fst cc, fst (snd cc)) (snd (snd cc))))).
  { exact (proj2 (proj2 Bu3 (fst cc, fst (snd cc)) (fst cc, fst (snd cc))
              (conj Hw (proj1 Hc)) _ _ (proj2 Hc))). }
  assert (HQ : dia Q ρ (fst (snd cc))
                 (snd (snd (tmden u ρ) (fst cc, fst (snd cc)) (snd (snd cc))))
               = true).
  { exact (eq_trans (eq_sym (dia_EEqE Q ρ ρ (fst (snd cc)) (fst (snd cc)) _ _
                       Hρ (proj1 Hc) HcntQ)) HB). }
  pose proof (Hu ρ ((fst cc, fst (snd cc)), snd (snd cc)) Hρ
                (conj (conj Hw (proj1 Hc)) (proj2 Hc))) as HU.
  pose proof (eq_trans (eq_sym (dia_imp (P ∧ Q) R ρ ρ
                (tmden u ρ) (tmden u ρ)
                ((fst cc, fst (snd cc)), snd (snd cc))
                ((fst cc, fst (snd cc)), snd (snd cc))
                Hρ HuD (conj (conj Hw (proj1 Hc)) (proj2 Hc)))) HU) as HU'.
  assert (Hand : dia (P ∧ Q) ρ (fst cc, fst (snd cc))
                   (snd (tmden u ρ) (fst cc, fst (snd cc)) (snd (snd cc)))
                 = true).
  { refine (eq_trans (dia_and P Q ρ ρ
              (fst cc, fst (snd cc)) (fst cc, fst (snd cc))
              (snd (tmden u ρ) (fst cc, fst (snd cc)) (snd (snd cc)))
              (snd (tmden u ρ) (fst cc, fst (snd cc)) (snd (snd cc)))
              Hρ (conj Hw (proj1 Hc))
              (proj2 HuD (fst cc, fst (snd cc)) (fst cc, fst (snd cc))
                 (conj Hw (proj1 Hc)) _ _ (proj2 Hc))) _).
    exact (f_equal2 andb HP HQ). }
  pose proof (implb_true_elim _ _ HU' Hand) as HR.
  assert (Hfw : EEq (W R)
      (fst (tmden (wk1 (S := W Q) (wk1 (S := W P) u))
              (fst (snd cc), (fst cc, ρ)))
         (fst cc, fst (snd cc)))
      (fst (tmden u ρ) (fst cc, fst (snd cc)))).
  { exact (proj1 Buq (fst cc, fst (snd cc)) (fst cc, fst (snd cc))
              (conj Hw (proj1 Hc))). }
  exact (eq_trans (dia_EEqE R ρ ρ _ _ (snd (snd cc)) (snd (snd cc))
                     Hρ Hfw (proj2 Hc)) HR).
Qed.

Lemma Valid_r_uncur : forall {Γ} {P Q R : prp Γ} (u : tm Γ (W (P ⊃ (Q ⊃ R)))),
    valid (P ⊃ (Q ⊃ R)) u -> valid (P ∧ Q ⊃ R) (r_uncur u).
Proof.
  intros Γ P Q R u Hu ρ cc Hρ Hcc.
  pose proof (proj1 Hcc) as Hw; pose proof (proj2 Hcc) as Hc.
  pose proof (tmden_EEqE u ρ ρ Hρ) as HuD.
  refine (eq_trans (dia_imp (P ∧ Q) R ρ ρ _ _ cc cc Hρ
            (tmden_EEqE (r_uncur u) ρ ρ Hρ) Hcc) _).
  destruct (dia (P ∧ Q) ρ (fst cc)
              (snd (tmden (r_uncur u) ρ) (fst cc) (snd cc))) eqn:HA;
    [| reflexivity].
  pose proof (tmden_wk1_EEq (S := W (P ∧ Q)) u (fst cc) (fst cc) ρ ρ Hw Hρ)
    as Bu1.
  pose proof (tmden_wk2_EEq (S1 := C R) (S2 := W (P ∧ Q)) u
                (snd cc) (snd cc) (fst cc) (fst cc) ρ ρ Hc Hw Hρ) as Bu2.
  pose proof (eq_trans (eq_sym (dia_and P Q ρ ρ (fst cc) (fst cc)
                (snd (tmden (r_uncur u) ρ) (fst cc) (snd cc))
                (snd (tmden (r_uncur u) ρ) (fst cc) (snd cc))
                Hρ Hw
                (proj2 (tmden_EEqE (r_uncur u) ρ ρ Hρ) _ _ Hw _ _ Hc))) HA)
    as H1.
  apply andb_true_iff in H1; destruct H1 as [HP' HQ'].
  assert (HP : dia P ρ (fst (fst cc))
                 (snd (tmden u ρ) (fst (fst cc)) (snd (fst cc), snd cc))
               = true).
  { refine (eq_trans (eq_sym (dia_EEqE P ρ ρ (fst (fst cc)) (fst (fst cc))
              _ _ Hρ (proj1 Hw)
              (proj2 Bu2 _ _ (proj1 Hw) (snd (fst cc), snd cc)
                 (snd (fst cc), snd cc) (conj (proj2 Hw) Hc)))) HP'). }
  assert (HQ : dia Q ρ (snd (fst cc))
                 (snd (fst (tmden u ρ) (fst (fst cc))) (snd (fst cc)) (snd cc))
               = true).
  { refine (eq_trans (eq_sym (dia_EEqE Q ρ ρ (snd (fst cc)) (snd (fst cc))
              _ _ Hρ (proj2 Hw)
              (proj2 (proj1 Bu2 _ _ (proj1 Hw)) _ _ (proj2 Hw) _ _ Hc)))
            HQ'). }
  pose proof (Hu ρ (fst (fst cc), (snd (fst cc), snd cc)) Hρ
                (conj (proj1 Hw) (conj (proj2 Hw) Hc))) as HU.
  pose proof (eq_trans (eq_sym (dia_imp P (Q ⊃ R) ρ ρ
                (tmden u ρ) (tmden u ρ)
                (fst (fst cc), (snd (fst cc), snd cc))
                (fst (fst cc), (snd (fst cc), snd cc))
                Hρ HuD (conj (proj1 Hw) (conj (proj2 Hw) Hc)))) HU) as HU'.
  pose proof (implb_true_elim _ _ HU' HP) as HQR.
  pose proof (eq_trans (eq_sym (dia_imp Q R ρ ρ
                (fst (tmden u ρ) (fst (fst cc)))
                (fst (tmden u ρ) (fst (fst cc)))
                (snd (fst cc), snd cc) (snd (fst cc), snd cc)
                Hρ (proj1 HuD _ _ (proj1 Hw))
                (conj (proj2 Hw) Hc))) HQR) as HQR'.
  pose proof (implb_true_elim _ _ HQR' HQ) as HR.
  assert (Hfw : EEq (W R)
      (fst (fst (tmden (wk1 (S := W (P ∧ Q)) u) (fst cc, ρ)) (fst (fst cc)))
         (snd (fst cc)))
      (fst (fst (tmden u ρ) (fst (fst cc))) (snd (fst cc)))).
  { exact (proj1 (proj1 Bu1 _ _ (proj1 Hw)) _ _ (proj2 Hw)). }
  exact (eq_trans (dia_EEqE R ρ ρ _ _ (snd cc) (snd cc) Hρ Hfw Hc) HR).
Qed.

Lemma Valid_r_and_contr : forall {Γ} {P : prp Γ},
    valid (P ⊃ P ∧ P) (r_and_contr (P := P)).
Proof.
  intros Γ P ρ cc Hρ Hcc.
  pose proof (proj1 Hcc) as Hw; pose proof (proj2 Hcc) as Hc.
  refine (eq_trans (dia_imp P (P ∧ P) ρ ρ _ _ cc cc Hρ
            (tmden_EEqE (r_and_contr (P := P)) ρ ρ Hρ) Hcc) _).
  destruct (dia P ρ (fst cc)
              (snd (tmden (r_and_contr (P := P)) ρ) (fst cc) (snd cc)))
    eqn:HA; [| reflexivity].
  pose proof (tmden_wk2_EEq (S1 := C (P ∧ P)) (S2 := W P) (diaT P)
                (snd cc) (snd cc) (fst cc) (fst cc) ρ ρ
                Hc Hw Hρ _ _ Hw _ _ (proj1 Hc)) as Hbr.
  refine (eq_trans (dia_and P P ρ ρ
            (fst (tmden (r_and_contr (P := P)) ρ) (fst cc))
            (fst cc, fst cc) (snd cc) (snd cc) Hρ (conj Hw Hw) Hc) _).
  cbn [fst snd].
  destruct (dia P ρ (fst cc) (fst (snd cc))) eqn:Htest.
  - assert (HAt : dia P ρ (fst cc) (snd (snd cc)) = true).
    { exact (eq_trans (eq_sym (f_equal (fun b : bool => dia P ρ (fst cc)
               (if b then snd (snd cc) else fst (snd cc)))
               (eq_trans Hbr Htest))) HA). }
    exact HAt.
  - exfalso.
    assert (HAt : dia P ρ (fst cc) (fst (snd cc)) = true).
    { exact (eq_trans (eq_sym (f_equal (fun b : bool => dia P ρ (fst cc)
               (if b then snd (snd cc) else fst (snd cc)))
               (eq_trans Hbr Htest))) HA). }
    rewrite HAt in Htest; discriminate.
Qed.

Lemma Valid_r_all_elim : forall {Γ} {Q : prp (tN :: Γ)} (t : tm Γ tN),
    valid (pAll Q ⊃ psub1 Q t) (r_all_elim (Q := Q) t).
Proof.
  intros Γ Q t ρ cc Hρ Hcc.
  pose proof (proj1 Hcc) as Hw; pose proof (proj2 Hcc) as Hc.
  pose proof (tmden_EEqE t ρ ρ Hρ) as HtD.
  refine (eq_trans (dia_imp (pAll Q) (psub1 Q t) ρ ρ _ _ cc cc Hρ
            (tmden_EEqE (r_all_elim (Q := Q) t) ρ ρ Hρ) Hcc) _).
  destruct (dia (pAll Q) ρ (fst cc)
              (snd (tmden (r_all_elim (Q := Q) t) ρ) (fst cc) (snd cc)))
    eqn:HA; [| reflexivity].
  assert (HcastC : EEq (C Q)
      (tmden ((tcast (C_sub (scons t) Q) v0)
                : tm (C (psub1 Q t) :: W (pAll Q) :: Γ) (C Q))
         (snd cc, (fst cc, ρ)))
      (tyden_cast (C_sub (scons t) Q) (snd cc))).
  { rewrite tmden_tcast; exact (EEq_cast _ _ _ Hc). }
  pose proof (tmden_wk2_EEq (S1 := C (psub1 Q t)) (S2 := W (pAll Q)) t
                (snd cc) (snd cc) (fst cc) (fst cc) ρ ρ Hc Hw Hρ) as Hwt.
  assert (HP : dia (pAll Q) ρ (fst cc)
                 (tmden t ρ, tyden_cast (C_sub (scons t) Q) (snd cc)) = true).
  { exact (eq_trans (eq_sym (dia_EEqE (pAll Q) ρ ρ (fst cc) (fst cc)
              (tmden (wk1 (S := C (psub1 Q t)) (wk1 (S := W (pAll Q)) t))
                 (snd cc, (fst cc, ρ)),
               tmden ((tcast (C_sub (scons t) Q) v0)
                        : tm (C (psub1 Q t) :: W (pAll Q) :: Γ) (C Q))
                 (snd cc, (fst cc, ρ)))
              (tmden t ρ, tyden_cast (C_sub (scons t) Q) (snd cc))
              Hρ Hw (conj Hwt HcastC))) HA). }
  pose proof (eq_trans (eq_sym (dia_all Q ρ ρ (fst cc) (fst cc)
                (tmden t ρ, tyden_cast (C_sub (scons t) Q) (snd cc))
                (tmden t ρ, tyden_cast (C_sub (scons t) Q) (snd cc))
                Hρ Hw (conj HtD (EEq_cast _ _ _ Hc)))) HP) as HP2.
  cbn [fst snd] in HP2.
  assert (Hfw : EEq (W (psub1 Q t))
      (tmden ((tcast (eq_sym (W_sub (scons t) Q)) (v0 · wk1 t))
                : tm (W (pAll Q) :: Γ) (W (psub1 Q t)))
         (fst cc, ρ))
      (tyden_cast (eq_sym (W_sub (scons t) Q)) (fst cc (tmden t ρ)))).
  { rewrite tmden_tcast.
    apply EEq_cast.
    exact (Hw _ _ (tmden_wk1_EEq (S := W (pAll Q)) t (fst cc) (fst cc)
                     ρ ρ Hw Hρ)). }
  refine (eq_trans (dia_psub1 Q t ρ ρ
            (fst (tmden (r_all_elim (Q := Q) t) ρ) (fst cc))
            (tyden_cast (eq_sym (W_sub (scons t) Q)) (fst cc (tmden t ρ)))
            (snd cc) (snd cc) Hρ Hfw Hc) _).
  rewrite tyden_cast_cancel_sym.
  exact HP2.
Qed.

Lemma Valid_r_ex_intro : forall {Γ} {Q : prp (tN :: Γ)} (t : tm Γ tN),
    valid (psub1 Q t ⊃ pEx Q) (r_ex_intro (Q := Q) t).
Proof.
  intros Γ Q t ρ cc Hρ Hcc.
  pose proof (proj1 Hcc) as Hw; pose proof (proj2 Hcc) as Hc.
  refine (eq_trans (dia_imp (psub1 Q t) (pEx Q) ρ ρ _ _ cc cc Hρ
            (tmden_EEqE (r_ex_intro (Q := Q) t) ρ ρ Hρ) Hcc) _).
  destruct (dia (psub1 Q t) ρ (fst cc)
              (snd (tmden (r_ex_intro (Q := Q) t) ρ) (fst cc) (snd cc)))
    eqn:HA; [| reflexivity].
  assert (HcastC : EEq (C (psub1 Q t))
      (tmden ((tcast (eq_sym (C_sub (scons t) Q)) v0)
                : tm (C Q :: W (psub1 Q t) :: Γ) (C (psub1 Q t)))
         (snd cc, (fst cc, ρ)))
      (tyden_cast (eq_sym (C_sub (scons t) Q)) (snd cc))).
  { rewrite tmden_tcast; exact (EEq_cast _ _ _ Hc). }
  assert (HP : dia (psub1 Q t) ρ (fst cc)
                 (tyden_cast (eq_sym (C_sub (scons t) Q)) (snd cc)) = true).
  { exact (eq_trans (eq_sym (dia_EEqE (psub1 Q t) ρ ρ (fst cc) (fst cc)
              (tmden ((tcast (eq_sym (C_sub (scons t) Q)) v0)
                        : tm (C Q :: W (psub1 Q t) :: Γ) (C (psub1 Q t)))
                 (snd cc, (fst cc, ρ)))
              (tyden_cast (eq_sym (C_sub (scons t) Q)) (snd cc))
              Hρ Hw HcastC)) HA). }
  pose proof (eq_trans (eq_sym (dia_psub1 Q t ρ ρ (fst cc) (fst cc)
                (tyden_cast (eq_sym (C_sub (scons t) Q)) (snd cc))
                (tyden_cast (eq_sym (C_sub (scons t) Q)) (snd cc))
                Hρ Hw (EEq_cast _ _ _ Hc))) HP) as HP2.
  rewrite tyden_cast_cancel_sym in HP2.
  assert (HcastW : EEq (W Q)
      (tmden ((tcast (W_sub (scons t) Q) v0)
                : tm (W (psub1 Q t) :: Γ) (W Q))
         (fst cc, ρ))
      (tyden_cast (W_sub (scons t) Q) (fst cc))).
  { rewrite tmden_tcast; exact (EEq_cast _ _ _ Hw). }
  pose proof (tmden_wk1_EEq (S := W (psub1 Q t)) t (fst cc) (fst cc) ρ ρ
                Hw Hρ) as Hwt.
  refine (eq_trans (dia_ex Q ρ ρ
            (fst (tmden (r_ex_intro (Q := Q) t) ρ) (fst cc))
            (tmden t ρ, tyden_cast (W_sub (scons t) Q) (fst cc))
            (snd cc) (snd cc) Hρ (conj Hwt HcastW) Hc) _).
  cbn [fst snd].
  exact HP2.
Qed.

Lemma Valid_r_leibniz : forall {Γ} {Q : prp (tN :: Γ)} (t s : tm Γ tN),
    valid (pEq t s ⊃ (psub1 Q t ⊃ psub1 Q s)) (r_leibniz (Q := Q) t s).
Proof.
  intros Γ Q t s ρ cc Hρ Hcc.
  pose proof (proj1 Hcc) as Hw; pose proof (proj2 Hcc) as Hc.
  refine (eq_trans (dia_imp (pEq t s) (psub1 Q t ⊃ psub1 Q s) ρ ρ _ _ cc cc
            Hρ (tmden_EEqE (r_leibniz (Q := Q) t s) ρ ρ Hρ) Hcc) _).
  match goal with
  | |- implb ?b _ = true => destruct b eqn:HA; [| reflexivity]
  end.
  assert (Heq : tmden t ρ = tmden s ρ).
  { exact (proj1 (teqb_true_iff ρ _ _)
             (eq_trans (eq_sym (dia_atom (teqb · t · s) ρ ρ (fst cc)
                (snd (tmden (r_leibniz (Q := Q) t s) ρ) (fst cc) (snd cc))
                Hρ)) HA)). }
  refine (eq_trans (dia_imp (psub1 Q t) (psub1 Q s) ρ ρ
            (fst (tmden (r_leibniz (Q := Q) t s) ρ) (fst cc))
            (fst (tmden (r_leibniz (Q := Q) t s) ρ) (fst cc))
            (snd cc) (snd cc) Hρ
            (proj1 (tmden_EEqE (r_leibniz (Q := Q) t s) ρ ρ Hρ) _ _ Hw) Hc)
    _).
  match goal with
  | |- implb ?b _ = true => destruct b eqn:HB; [| reflexivity]
  end.
  assert (HcastC : EEq (C (psub1 Q t))
      (tmden ((tcast (eq_trans (C_sub (scons s) Q) (eq_sym (C_sub (scons t) Q)))
                 v0)
                : tm (C (psub1 Q s) :: W (psub1 Q t) :: W (pEq t s) :: Γ)
                     (C (psub1 Q t)))
         (snd (snd cc), (fst (snd cc), (fst cc, ρ))))
      (tyden_cast (eq_trans (C_sub (scons s) Q) (eq_sym (C_sub (scons t) Q)))
         (snd (snd cc)))).
  { rewrite tmden_tcast; exact (EEq_cast _ _ _ (proj2 Hc)). }
  assert (HBt : dia (psub1 Q t) ρ (fst (snd cc))
      (tyden_cast (eq_trans (C_sub (scons s) Q) (eq_sym (C_sub (scons t) Q)))
         (snd (snd cc))) = true).
  { exact (eq_trans (eq_sym (dia_EEqE (psub1 Q t) ρ ρ
              (fst (snd cc)) (fst (snd cc))
              (tmden ((tcast (eq_trans (C_sub (scons s) Q)
                                (eq_sym (C_sub (scons t) Q))) v0)
                        : tm (C (psub1 Q s) :: W (psub1 Q t)
                              :: W (pEq t s) :: Γ) (C (psub1 Q t)))
                 (snd (snd cc), (fst (snd cc), (fst cc, ρ))))
              (tyden_cast (eq_trans (C_sub (scons s) Q)
                             (eq_sym (C_sub (scons t) Q))) (snd (snd cc)))
              Hρ (proj1 Hc) HcastC)) HB). }
  pose proof (eq_trans (eq_sym (dia_psub1 Q t ρ ρ
                (fst (snd cc)) (fst (snd cc))
                (tyden_cast (eq_trans (C_sub (scons s) Q)
                               (eq_sym (C_sub (scons t) Q))) (snd (snd cc)))
                (tyden_cast (eq_trans (C_sub (scons s) Q)
                               (eq_sym (C_sub (scons t) Q))) (snd (snd cc)))
                Hρ (proj1 Hc) (EEq_cast _ _ _ (proj2 Hc)))) HBt) as HB2.
  rewrite tyden_cast_trans in HB2.
  rewrite (ty_uip (eq_trans (eq_trans (C_sub (scons s) Q)
                     (eq_sym (C_sub (scons t) Q))) (C_sub (scons t) Q))
             (C_sub (scons s) Q)) in HB2.
  assert (HfwW : EEq (W (psub1 Q s))
      (tmden ((tcast (eq_trans (W_sub (scons t) Q) (eq_sym (W_sub (scons s) Q)))
                 v0)
                : tm (W (psub1 Q t) :: W (pEq t s) :: Γ) (W (psub1 Q s)))
         (fst (snd cc), (fst cc, ρ)))
      (tyden_cast (eq_trans (W_sub (scons t) Q) (eq_sym (W_sub (scons s) Q)))
         (fst (snd cc)))).
  { rewrite tmden_tcast; exact (EEq_cast _ _ _ (proj1 Hc)). }
  refine (eq_trans (dia_psub1 Q s ρ ρ
            (fst (fst (tmden (r_leibniz (Q := Q) t s) ρ) (fst cc))
               (fst (snd cc)))
            (tyden_cast (eq_trans (W_sub (scons t) Q)
                           (eq_sym (W_sub (scons s) Q))) (fst (snd cc)))
            (snd (snd cc)) (snd (snd cc)) Hρ HfwW (proj2 Hc)) _).
  rewrite tyden_cast_trans.
  rewrite (ty_uip (eq_trans (eq_trans (W_sub (scons t) Q)
                     (eq_sym (W_sub (scons s) Q))) (W_sub (scons s) Q))
             (W_sub (scons t) Q)).
  exact (eq_trans (eq_sym (f_equal (fun n => dia Q (n, ρ)
            (tyden_cast (W_sub (scons t) Q) (fst (snd cc)))
            (tyden_cast (C_sub (scons s) Q) (snd (snd cc)))) Heq)) HB2).
Qed.

Lemma Valid_r_all_intro : forall {Γ} {P : prp Γ} {Q : prp (tN :: Γ)}
    (u : tm (tN :: Γ) (W (pwk P ⊃ Q))),
    valid (pwk P ⊃ Q) u -> valid (P ⊃ pAll Q) (r_all_intro u).
Proof.
  intros Γ P Q u Hu ρ cc Hρ Hcc.
  pose proof (proj1 Hcc) as Hw; pose proof (proj2 Hcc) as Hc.
  pose proof (conj (proj1 Hc) Hρ) as Hρn.
  pose proof (tmden_EEqE u (fst (snd cc), ρ) (fst (snd cc), ρ) Hρn) as HuD.
  refine (eq_trans (dia_imp P (pAll Q) ρ ρ _ _ cc cc Hρ
            (tmden_EEqE (r_all_intro u) ρ ρ Hρ) Hcc) _).
  match goal with
  | |- implb ?b _ = true => destruct b eqn:HA; [| reflexivity]
  end.
  assert (Eg : EEqE (tN :: Γ)
      (subden (sub_at0 (drop_prefix [_; _]) ((tfst v0) : tm (C (pAll Q) :: W P :: Γ) tN))
         (snd cc, (fst cc, ρ)))
      (fst (snd cc), ρ)).
  { pose proof (subden_sub_at0 (drop_prefix [_; _])
                  ((tfst v0) : tm (C (pAll Q) :: W P :: Γ) tN)
                  (snd cc, (fst cc, ρ)) (snd cc, (fst cc, ρ))
                  (conj Hc (conj Hw Hρ))) as E2.
    rewrite opeden_drop_prefix in E2.
    exact E2. }
  pose proof (EEq_trans _ _ _ _
                (tmden_subst u
                   (sub_at0 (drop_prefix [_; _]) ((tfst v0) : tm (C (pAll Q) :: W P :: Γ) tN))
                   (snd cc, (fst cc, ρ)) (snd cc, (fst cc, ρ))
                   (conj Hc (conj Hw Hρ)))
                (tmden_EEqE u _ _ Eg)) as Bg.
  assert (HcastW : EEq (W (pwk (S := tN) P))
      (tmden ((tcast (eq_sym (W_ren wk P)) v1)
                : tm (C (pAll Q) :: W P :: Γ) (W (pwk (S := tN) P)))
         (snd cc, (fst cc, ρ)))
      (tyden_cast (eq_sym (W_ren wk P)) (fst cc))).
  { rewrite tmden_tcast; exact (EEq_cast _ _ _ Hw). }
  assert (HP : dia P ρ (fst cc)
      (tyden_cast (C_ren wk P)
         (snd (tmden u (fst (snd cc), ρ))
            (tyden_cast (eq_sym (W_ren wk P)) (fst cc)) (snd (snd cc))))
      = true).
  { refine (eq_trans (eq_sym (dia_EEqE P ρ ρ (fst cc) (fst cc)
              (tmden ((tcast (C_ren wk P)
                         (tsnd (subst (sub_at0 (drop_prefix [_; _])
                                  ((tfst v0)
                                     : tm (C (pAll Q) :: W P :: Γ) tN)) u)
                            · tcast (eq_sym (W_ren wk P)) v1 · tsnd v0))
                        : tm (C (pAll Q) :: W P :: Γ) (C P))
                 (snd cc, (fst cc, ρ)))
              (tyden_cast (C_ren wk P)
                 (snd (tmden u (fst (snd cc), ρ))
                    (tyden_cast (eq_sym (W_ren wk P)) (fst cc))
                    (snd (snd cc))))
              Hρ Hw _)) HA).
    rewrite tmden_tcast.
    apply EEq_cast.
    exact (proj2 Bg _ _ HcastW _ _ (proj2 Hc)). }
  pose proof (Hu (fst (snd cc), ρ)
                (tyden_cast (eq_sym (W_ren wk P)) (fst cc), snd (snd cc))
                Hρn (conj (EEq_cast _ _ _ Hw) (proj2 Hc))) as HU.
  pose proof (eq_trans (eq_sym (dia_imp (pwk P) Q (fst (snd cc), ρ)
                (fst (snd cc), ρ) (tmden u (fst (snd cc), ρ))
                (tmden u (fst (snd cc), ρ))
                (tyden_cast (eq_sym (W_ren wk P)) (fst cc), snd (snd cc))
                (tyden_cast (eq_sym (W_ren wk P)) (fst cc), snd (snd cc))
                Hρn HuD (conj (EEq_cast _ _ _ Hw) (proj2 Hc)))) HU) as HU'.
  cbn [fst snd] in HU'.
  pose proof (dia_pwk (S := tN) P (fst (snd cc)) (fst (snd cc)) ρ ρ
                (tyden_cast (eq_sym (W_ren wk P)) (fst cc))
                (tyden_cast (eq_sym (W_ren wk P)) (fst cc))
                (snd (tmden u (fst (snd cc), ρ))
                   (tyden_cast (eq_sym (W_ren wk P)) (fst cc)) (snd (snd cc)))
                (snd (tmden u (fst (snd cc), ρ))
                   (tyden_cast (eq_sym (W_ren wk P)) (fst cc)) (snd (snd cc)))
                (proj1 Hc) Hρ (EEq_cast _ _ _ Hw)
                (proj2 HuD _ _ (EEq_cast _ _ _ Hw) _ _ (proj2 Hc))) as E3.
  rewrite tyden_cast_cancel_sym in E3.
  pose proof (implb_true_elim _ _ HU' (eq_trans E3 HP)) as HQ.
  refine (eq_trans (dia_all Q ρ ρ
            (fst (tmden (r_all_intro u) ρ) (fst cc))
            (fst (tmden (r_all_intro u) ρ) (fst cc))
            (snd cc) (snd cc) Hρ
            (proj1 (tmden_EEqE (r_all_intro u) ρ ρ Hρ) _ _ Hw) Hc) _).
  assert (Ef : EEqE (tN :: Γ)
      (subden (sub_at0 (drop_prefix [_; _]) ((v0) : tm (tN :: W P :: Γ) tN))
         (fst (snd cc), (fst cc, ρ)))
      (fst (snd cc), ρ)).
  { pose proof (subden_sub_at0 (drop_prefix [_; _]) ((v0) : tm (tN :: W P :: Γ) tN)
                  (fst (snd cc), (fst cc, ρ)) (fst (snd cc), (fst cc, ρ))
                  (conj (proj1 Hc) (conj Hw Hρ))) as E4.
    rewrite opeden_drop_prefix in E4.
    exact E4. }
  pose proof (EEq_trans _ _ _ _
                (tmden_subst u
                   (sub_at0 (drop_prefix [_; _]) ((v0) : tm (tN :: W P :: Γ) tN))
                   (fst (snd cc), (fst cc, ρ)) (fst (snd cc), (fst cc, ρ))
                   (conj (proj1 Hc) (conj Hw Hρ)))
                (tmden_EEqE u _ _ Ef)) as Bf.
  assert (HcastWf : EEq (W (pwk (S := tN) P))
      (tmden ((tcast (eq_sym (W_ren wk P)) v1)
                : tm (tN :: W P :: Γ) (W (pwk (S := tN) P)))
         (fst (snd cc), (fst cc, ρ)))
      (tyden_cast (eq_sym (W_ren wk P)) (fst cc))).
  { rewrite tmden_tcast; exact (EEq_cast _ _ _ Hw). }
  exact (eq_trans (dia_EEqE Q (fst (snd cc), ρ) (fst (snd cc), ρ) _ _
            (snd (snd cc)) (snd (snd cc)) Hρn
            (proj1 Bf _ _ HcastWf) (proj2 Hc)) HQ).
Qed.

Lemma Valid_r_ex_elim : forall {Γ} {P : prp Γ} {Q : prp (tN :: Γ)}
    (u : tm (tN :: Γ) (W (Q ⊃ pwk P))),
    valid (Q ⊃ pwk P) u -> valid (pEx Q ⊃ P) (r_ex_elim u).
Proof.
  intros Γ P Q u Hu ρ cc Hρ Hcc.
  pose proof (proj1 Hcc) as Hw; pose proof (proj2 Hcc) as Hc.
  pose proof (conj (proj1 Hw) Hρ) as Hρn.
  pose proof (tmden_EEqE u (fst (fst cc), ρ) (fst (fst cc), ρ) Hρn) as HuD.
  refine (eq_trans (dia_imp (pEx Q) P ρ ρ _ _ cc cc Hρ
            (tmden_EEqE (r_ex_elim u) ρ ρ Hρ) Hcc) _).
  match goal with
  | |- implb ?b _ = true => destruct b eqn:HA; [| reflexivity]
  end.
  assert (Eg : EEqE (tN :: Γ)
      (subden (sub_at0 (drop_prefix [_; _]) ((tfst v1) : tm (C P :: W (pEx Q) :: Γ) tN))
         (snd cc, (fst cc, ρ)))
      (fst (fst cc), ρ)).
  { pose proof (subden_sub_at0 (drop_prefix [_; _])
                  ((tfst v1) : tm (C P :: W (pEx Q) :: Γ) tN)
                  (snd cc, (fst cc, ρ)) (snd cc, (fst cc, ρ))
                  (conj Hc (conj Hw Hρ))) as E2.
    rewrite opeden_drop_prefix in E2.
    exact E2. }
  pose proof (EEq_trans _ _ _ _
                (tmden_subst u
                   (sub_at0 (drop_prefix [_; _]) ((tfst v1) : tm (C P :: W (pEx Q) :: Γ) tN))
                   (snd cc, (fst cc, ρ)) (snd cc, (fst cc, ρ))
                   (conj Hc (conj Hw Hρ)))
                (tmden_EEqE u _ _ Eg)) as Bg.
  assert (HcastC : EEq (C (pwk (S := tN) P))
      (tmden ((tcast (eq_sym (C_ren wk P)) v0)
                : tm (C P :: W (pEx Q) :: Γ) (C (pwk (S := tN) P)))
         (snd cc, (fst cc, ρ)))
      (tyden_cast (eq_sym (C_ren wk P)) (snd cc))).
  { rewrite tmden_tcast; exact (EEq_cast _ _ _ Hc). }
  assert (HP : dia (pEx Q) ρ (fst cc)
      (snd (tmden u (fst (fst cc), ρ)) (snd (fst cc))
         (tyden_cast (eq_sym (C_ren wk P)) (snd cc))) = true).
  { refine (eq_trans (eq_sym (dia_EEqE (pEx Q) ρ ρ (fst cc) (fst cc)
              (tmden ((tsnd (subst (sub_at0 (drop_prefix [_; _])
                          ((tfst v1) : tm (C P :: W (pEx Q) :: Γ) tN)) u)
                         · tsnd v1 · tcast (eq_sym (C_ren wk P)) v0)
                        : tm (C P :: W (pEx Q) :: Γ) (C (pEx Q)))
                 (snd cc, (fst cc, ρ)))
              (snd (tmden u (fst (fst cc), ρ)) (snd (fst cc))
                 (tyden_cast (eq_sym (C_ren wk P)) (snd cc)))
              Hρ Hw _)) HA).
    exact (proj2 Bg _ _ (proj2 Hw) _ _ HcastC). }
  pose proof (eq_trans (eq_sym (dia_ex Q ρ ρ (fst cc) (fst cc)
                (snd (tmden u (fst (fst cc), ρ)) (snd (fst cc))
                   (tyden_cast (eq_sym (C_ren wk P)) (snd cc)))
                (snd (tmden u (fst (fst cc), ρ)) (snd (fst cc))
                   (tyden_cast (eq_sym (C_ren wk P)) (snd cc)))
                Hρ Hw
                (proj2 HuD _ _ (proj2 Hw) _ _ (EEq_cast _ _ _ Hc)))) HP)
    as HP2.
  cbn [fst snd] in HP2.
  pose proof (Hu (fst (fst cc), ρ)
                (snd (fst cc), tyden_cast (eq_sym (C_ren wk P)) (snd cc))
                Hρn (conj (proj2 Hw) (EEq_cast _ _ _ Hc))) as HU.
  pose proof (eq_trans (eq_sym (dia_imp Q (pwk P) (fst (fst cc), ρ)
                (fst (fst cc), ρ) (tmden u (fst (fst cc), ρ))
                (tmden u (fst (fst cc), ρ))
                (snd (fst cc), tyden_cast (eq_sym (C_ren wk P)) (snd cc))
                (snd (fst cc), tyden_cast (eq_sym (C_ren wk P)) (snd cc))
                Hρn HuD (conj (proj2 Hw) (EEq_cast _ _ _ Hc)))) HU) as HU'.
  cbn [fst snd] in HU'.
  pose proof (implb_true_elim _ _ HU' HP2) as Hpwk.
  pose proof (dia_pwk (S := tN) P (fst (fst cc)) (fst (fst cc)) ρ ρ
                (fst (tmden u (fst (fst cc), ρ)) (snd (fst cc)))
                (fst (tmden u (fst (fst cc), ρ)) (snd (fst cc)))
                (tyden_cast (eq_sym (C_ren wk P)) (snd cc))
                (tyden_cast (eq_sym (C_ren wk P)) (snd cc))
                (proj1 Hw) Hρ (proj1 HuD _ _ (proj2 Hw))
                (EEq_cast _ _ _ Hc)) as E3.
  rewrite tyden_cast_cancel_sym in E3.
  pose proof (eq_trans (eq_sym E3) Hpwk) as HPP.
  assert (Ef : EEqE (tN :: Γ)
      (subden (sub_at0 wk ((tfst v0) : tm (W (pEx Q) :: Γ) tN))
         (fst cc, ρ))
      (fst (fst cc), ρ)).
  { pose proof (subden_sub_at0 wk ((tfst v0) : tm (W (pEx Q) :: Γ) tN)
                  (fst cc, ρ) (fst cc, ρ) (conj Hw Hρ)) as E4.
    rewrite opeden_wk in E4.
    exact E4. }
  pose proof (EEq_trans _ _ _ _
                (tmden_subst u
                   (sub_at0 wk ((tfst v0) : tm (W (pEx Q) :: Γ) tN))
                   (fst cc, ρ) (fst cc, ρ) (conj Hw Hρ))
                (tmden_EEqE u _ _ Ef)) as Bf.
  assert (Hfw : EEq (W P)
      (tmden ((tcast (W_ren wk P)
                 (tfst (subst (sub_at0 wk
                          ((tfst v0) : tm (W (pEx Q) :: Γ) tN)) u)
                    · tsnd v0))
                : tm (W (pEx Q) :: Γ) (W P))
         (fst cc, ρ))
      (tyden_cast (W_ren wk P)
         (fst (tmden u (fst (fst cc), ρ)) (snd (fst cc))))).
  { rewrite tmden_tcast.
    apply EEq_cast.
    exact (proj1 Bf _ _ (proj2 Hw)). }
  exact (eq_trans (dia_EEqE P ρ ρ _ _ (snd cc) (snd cc) Hρ Hfw Hc) HPP).
Qed.

(** ** Atomic conversion

    [ax_conv] reuses the underlying realizer, so validity only has to move
    the matrix across [defeq] of the atoms — precisely [tmden_defeq], with
    [EEq] at [tBool] being Leibniz equality. *)

Lemma Valid_conv : forall {Γ} {b b' : tm Γ tBool},
    defeq Γ tBool b b' ->
    forall t : tm Γ (W (pAtom b)),
    valid (pAtom b) t -> valid (pAtom b') t.
Proof.
  intros Γ b b' e t Hv ρ c Hρ Hc.
  refine (eq_trans (dia_atom b' ρ ρ (tmden t ρ) c Hρ) _).
  refine (eq_trans (eq_sym (tmden_defeq b b' e ρ ρ Hρ)) _).
  refine (eq_trans (eq_sym (dia_atom b ρ ρ (tmden t ρ) c Hρ)) _).
  exact (Hv ρ c Hρ Hc).
Qed.

(** ** D3: the characteristic principles

    The syntactic [wtriv]/[ctriv] side conditions entail PER-triviality of the
    corresponding move types. Markov uses both conditions; IP needs only
    witness-triviality of its universal premise, while [Q] is unrestricted
    because existential counters are non-dependent in this interpretation. *)

Lemma Valid_r_markov_generalized : forall {Γ} (P : prp (tN :: Γ)),
    wtriv P = true -> ctriv P = true ->
    valid (pNot (pAll (pNot P)) ⊃ pEx P) (r_markov P).
Proof.
  intros Γ P HwP HcP ρ cc Hρ Hcc.
  pose proof (proj1 (wtriv_ctriv_triv P) HwP) as HWt.
  pose proof (proj2 (wtriv_ctriv_triv P) HcP) as HCt.
  pose proof (proj1 Hcc) as Hw; pose proof (proj2 Hcc) as Hc.
  refine (eq_trans (dia_imp (pNot (pAll (pNot P))) (pEx P)
            ρ ρ _ _ cc cc Hρ (tmden_EEqE (r_markov P) ρ ρ Hρ) Hcc) _).
  match goal with
  | |- implb ?bb _ = true => destruct bb eqn:HA; [| reflexivity]
  end.
  set (U := tmden (Γ := C (pEx P) :: W (pNot (pAll (pNot P))) :: Γ)
              (tdefault (W (pAll (pNot P))))
              (snd cc, (fst cc, ρ))).
  set (V := tmden (Γ := W (pNot (pAll (pNot P))) :: Γ)
              (tdefault (W (pAll (pNot P)))) (fst cc, ρ)).
  assert (BU : EEq (W (pAll (pNot P))) U U).
  { exact (EEq_refl_l _ _ _
      (tmden_tdefault (W (pAll (pNot P)))
         (Γ := C (pEx P) :: W (pNot (pAll (pNot P))) :: Γ)
         (snd cc, (fst cc, ρ)))). }
  assert (BVU : EEq (W (pAll (pNot P))) V U).
  { exact (EEq_trans _ _ _ _
      (tmden_tdefault (W (pAll (pNot P)))
         (Γ := W (pNot (pAll (pNot P))) :: Γ) (fst cc, ρ))
      (EEq_sym _ _ _
        (tmden_tdefault (W (pAll (pNot P)))
           (Γ := C (pEx P) :: W (pNot (pAll (pNot P))) :: Γ)
           (snd cc, (fst cc, ρ))))). }
  pose proof (eq_trans (eq_sym (dia_imp (pAll (pNot P)) pFalse ρ ρ
                (fst cc) (fst cc) (U, tt) (U, tt)
                Hρ Hw (conj BU eq_refl))) HA) as H1.
  cbn [fst snd] in H1.
  pose proof (eq_trans (eq_sym (f_equal
                (implb (dia (pAll (pNot P)) ρ U (snd (fst cc) U tt)))
                (dia_atom tfalse ρ ρ (fst (fst cc) U) tt Hρ))) H1) as H2.
  pose proof (proj1 (negb_true_iff _)
                (eq_trans (eq_sym (implb_false_r _)) H2)) as H3.
  pose proof (eq_trans (eq_sym (dia_all (pNot P) ρ ρ U U
                (snd (fst cc) U tt) (snd (fst cc) U tt)
                Hρ BU (proj2 Hw _ _ BU _ _ eq_refl))) H3) as H4.
  pose proof (eq_trans (eq_sym (dia_imp P pFalse
                (fst (snd (fst cc) U tt), ρ) (fst (snd (fst cc) U tt), ρ)
                (U (fst (snd (fst cc) U tt))) (U (fst (snd (fst cc) U tt)))
                (snd (snd (fst cc) U tt)) (snd (snd (fst cc) U tt))
                (conj eq_refl Hρ) (BU _ _ eq_refl)
                (proj2 (proj2 Hw _ _ BU _ _ eq_refl)))) H4) as H5.
  pose proof (eq_trans (eq_sym (f_equal
                (implb (dia P (fst (snd (fst cc) U tt), ρ)
                          (fst (snd (snd (fst cc) U tt)))
                          (snd (U (fst (snd (fst cc) U tt)))
                             (fst (snd (snd (fst cc) U tt)))
                             (snd (snd (snd (fst cc) U tt))))))
                (dia_atom (Γ := tN :: Γ) tfalse
                   (fst (snd (fst cc) U tt), ρ)
                   (fst (snd (fst cc) U tt), ρ) _ _ (conj eq_refl Hρ))))
                H5) as H6.
  pose proof (proj1 (negb_false_iff _)
                (eq_trans (eq_sym (implb_false_r _)) H6)) as H7.
  refine (eq_trans (dia_ex P ρ ρ
            (fst (tmden (r_markov P) ρ) (fst cc))
            (fst (tmden (r_markov P) ρ) (fst cc))
            (snd cc) (snd cc) Hρ
            (proj1 (tmden_EEqE (r_markov P) ρ ρ Hρ) _ _ Hw) Hc) _).
  refine (eq_trans (dia_EEqE P
            (fst (fst (tmden (r_markov P) ρ) (fst cc)), ρ)
            (fst (snd (fst cc) U tt), ρ)
            (snd (fst (tmden (r_markov P) ρ) (fst cc)))
            (fst (snd (snd (fst cc) U tt)))
            (snd cc)
            (snd (U (fst (snd (fst cc) U tt)))
               (fst (snd (snd (fst cc) U tt)))
               (snd (snd (snd (fst cc) U tt))))
            (conj (proj1 (proj2 Hw _ _ BVU _ _ (@eq_refl unit tt))) Hρ)
            (triv_EEq (W P) HWt _ _)
            (triv_EEq (C P) HCt _ _)) _).
  exact H7.
Qed.

Corollary Valid_r_markov_atomic : forall {Γ} (b : tm (tN :: Γ) tBool),
    valid (pNot (pAll (pNot (pAtom b))) ⊃ pEx (pAtom b))
          (r_markov_atomic b).
Proof.
  intros Γ b; apply Valid_r_markov_generalized; reflexivity.
Qed.

Lemma Valid_r_ip_generalized : forall {Γ} (P Q : prp (tN :: Γ)),
    wtriv P = true ->
    valid ((pAll P ⊃ pEx Q) ⊃ pEx (pwk (S := tN) (pAll P) ⊃ Q)) (r_ip P Q).
Proof.
  intros Γ P Q HwP ρ cc Hρ Hcc.
  pose proof (proj1 (wtriv_ctriv_triv P) HwP) as HWt.
  pose proof (proj1 Hcc) as Hw; pose proof (proj2 Hcc) as Hc.
  refine (eq_trans (dia_imp (pAll P ⊃ pEx Q)
            (pEx (pwk (S := tN) (pAll P) ⊃ Q))
            ρ ρ _ _ cc cc Hρ (tmden_EEqE (r_ip P Q) ρ ρ Hρ) Hcc) _).
  match goal with
  | |- implb ?bb _ = true => destruct bb eqn:HA; [| reflexivity]
  end.
  set (U := tmden (Γ := C (pEx (pwk (S := tN) (pAll P) ⊃ Q))
                        :: W (pAll P ⊃ pEx Q) :: Γ)
              (tdefault (W (pAll P))) (snd cc, (fst cc, ρ))).
  set (V := tmden (Γ := W (pAll P ⊃ pEx Q) :: Γ)
              (tdefault (W (pAll P))) (fst cc, ρ)).
  set (Vf := tmden (Γ := W (pwk (S := tN) (pAll P))
                         :: W (pAll P ⊃ pEx Q) :: Γ)
               (tdefault (W (pAll P))) (fst (snd cc), (fst cc, ρ))).
  set (Wg := tmden (Γ := C Q :: W (pwk (S := tN) (pAll P))
                         :: W (pAll P ⊃ pEx Q) :: Γ)
               (tdefault (W (pAll P)))
               (snd (snd cc), (fst (snd cc), (fst cc, ρ)))).
  assert (BU : EEq (W (pAll P)) U U).
  { exact (EEq_refl_l _ _ _ (tmden_tdefault (W (pAll P))
      (Γ := C (pEx (pwk (S := tN) (pAll P) ⊃ Q))
            :: W (pAll P ⊃ pEx Q) :: Γ)
      (snd cc, (fst cc, ρ)))). }
  assert (BVU : EEq (W (pAll P)) V U).
  { exact (EEq_trans _ _ _ _
      (tmden_tdefault (W (pAll P))
         (Γ := W (pAll P ⊃ pEx Q) :: Γ) (fst cc, ρ))
      (EEq_sym _ _ _ (tmden_tdefault (W (pAll P))
         (Γ := C (pEx (pwk (S := tN) (pAll P) ⊃ Q))
               :: W (pAll P ⊃ pEx Q) :: Γ)
         (snd cc, (fst cc, ρ))))). }
  assert (BVfU : EEq (W (pAll P)) Vf U).
  { exact (EEq_trans _ _ _ _
      (tmden_tdefault (W (pAll P))
         (Γ := W (pwk (S := tN) (pAll P)) :: W (pAll P ⊃ pEx Q) :: Γ)
         (fst (snd cc), (fst cc, ρ)))
      (EEq_sym _ _ _ (tmden_tdefault (W (pAll P))
         (Γ := C (pEx (pwk (S := tN) (pAll P) ⊃ Q))
               :: W (pAll P ⊃ pEx Q) :: Γ)
         (snd cc, (fst cc, ρ))))). }
  assert (BWU : EEq (W (pAll P)) Wg U).
  { exact (EEq_trans _ _ _ _
      (tmden_tdefault (W (pAll P))
         (Γ := C Q :: W (pwk (S := tN) (pAll P))
               :: W (pAll P ⊃ pEx Q) :: Γ)
         (snd (snd cc), (fst (snd cc), (fst cc, ρ))))
      (EEq_sym _ _ _ (tmden_tdefault (W (pAll P))
         (Γ := C (pEx (pwk (S := tN) (pAll P) ⊃ Q))
               :: W (pAll P ⊃ pEx Q) :: Γ)
         (snd cc, (fst cc, ρ))))). }
  pose proof (eq_trans (eq_sym (dia_imp (pAll P) (pEx Q)
                ρ ρ (fst cc) (fst cc)
                (U, snd (snd cc)) (U, snd (snd cc))
                Hρ Hw (conj BU (proj2 Hc)))) HA) as H1.
  cbn [fst snd] in H1.
  refine (eq_trans (dia_ex (pwk (S := tN) (pAll P) ⊃ Q) ρ ρ
            (fst (tmden (r_ip P Q) ρ) (fst cc))
            (fst (tmden (r_ip P Q) ρ) (fst cc))
            (snd cc) (snd cc) Hρ
            (proj1 (tmden_EEqE (r_ip P Q) ρ ρ Hρ) _ _ Hw) Hc) _).
  refine (eq_trans (dia_imp (pwk (S := tN) (pAll P)) Q
            (fst (fst (tmden (r_ip P Q) ρ) (fst cc)), ρ)
            (fst (fst (tmden (r_ip P Q) ρ) (fst cc)), ρ)
            (snd (fst (tmden (r_ip P Q) ρ) (fst cc)))
            (snd (fst (tmden (r_ip P Q) ρ) (fst cc)))
            (snd cc) (snd cc)
            (conj eq_refl Hρ)
            (proj2 (proj1 (tmden_EEqE (r_ip P Q) ρ ρ Hρ) _ _ Hw))
            Hc) _).
  match goal with
  | |- implb ?bb _ = true => destruct bb eqn:HB; [| reflexivity]
  end.
  destruct (dia (pAll P) ρ U (snd (fst cc) U (snd (snd cc)))) eqn:HP.
  - (* the universal held at the canonical family: use the ∃ from H1 *)
    pose proof (implb_true_elim _ _ H1 eq_refl) as H2.
    pose proof (eq_trans (eq_sym (dia_ex Q ρ ρ
                  (fst (fst cc) U) (fst (fst cc) U)
                  (snd (snd cc)) (snd (snd cc))
                  Hρ (proj1 Hw _ _ BU) (proj2 Hc))) H2) as H3.
    refine (eq_trans (dia_EEqE Q
              (fst (fst (tmden (r_ip P Q) ρ) (fst cc)), ρ)
              (fst (fst (fst cc) U), ρ)
              (fst (snd (fst (tmden (r_ip P Q) ρ) (fst cc))) (fst (snd cc)))
              (snd (fst (fst cc) U))
              (snd (snd cc)) (snd (snd cc))
              (conj (proj1 (proj1 Hw _ _ BVU)) Hρ)
              (proj2 (proj1 Hw _ _ BVfU))
              (proj2 Hc)) _).
    exact H3.
  - (* it failed — but the goal's antecedent HB says it holds: contradict *)
    exfalso.
    pose proof (dia_pren (pAll P) (wk (S := tN))
                  (fst (fst (tmden (r_ip P Q) ρ) (fst cc)), ρ)
                  (fst (fst (tmden (r_ip P Q) ρ) (fst cc)), ρ)
                  (fst (snd cc)) (fst (snd cc))
                  (snd (snd (fst (tmden (r_ip P Q) ρ) (fst cc)))
                     (fst (snd cc)) (snd (snd cc)))
                  (snd (snd (fst (tmden (r_ip P Q) ρ) (fst cc)))
                     (fst (snd cc)) (snd (snd cc)))
                  (conj eq_refl Hρ) (proj1 Hc)
                  (proj2 (proj2 (proj1 (tmden_EEqE (r_ip P Q) ρ ρ Hρ)
                             _ _ Hw)) _ _ (proj1 Hc) _ _ (proj2 Hc)))
      as E5.
    pose proof (eq_trans (eq_sym E5) HB) as H5.
    pose proof (eq_trans (eq_sym (f_equal
                  (fun e => dia (pAll P) e
                     (tyden_cast (W_ren (wk (S := tN)) (pAll P))
                        (fst (snd cc)))
                     (tyden_cast (C_ren (wk (S := tN)) (pAll P))
                        (snd (snd (fst (tmden (r_ip P Q) ρ) (fst cc)))
                           (fst (snd cc)) (snd (snd cc)))))
                  (opeden_wk (S := tN)
                     (fst (fst (tmden (r_ip P Q) ρ) (fst cc)), ρ))))
                H5) as H6.
    pose proof (f_equal (fun k => dia (pAll P) ρ
                   (tyden_cast (W_ren (wk (S := tN)) (pAll P))
                      (fst (snd cc)))
                   k)
                  (eq_trans
                     (f_equal (tyden_cast (C_ren (wk (S := tN)) (pAll P)))
                        (tmden_tcast (eq_sym (C_ren (wk (S := tN)) (pAll P)))
                           ((tsnd v2 · tdefault (W (pAll P)) · v0)
                              : tm (C Q :: W (pwk (S := tN) (pAll P))
                                    :: W (pAll P ⊃ pEx Q) :: Γ) (C (pAll P)))
                           (snd (snd cc), (fst (snd cc), (fst cc, ρ)))))
                     (tyden_cast_cancel_sym
                        (C_ren (wk (S := tN)) (pAll P))
                        (tmden ((tsnd v2 · tdefault (W (pAll P)) · v0)
                                  : tm (C Q :: W (pwk (S := tN) (pAll P))
                                        :: W (pAll P ⊃ pEx Q) :: Γ)
                                       (C (pAll P)))
                           (snd (snd cc), (fst (snd cc), (fst cc, ρ)))))))
      as CE.
    pose proof (eq_trans (eq_sym CE) H6) as H7.
    pose proof (eq_trans (eq_sym (dia_all P ρ ρ
                  (tyden_cast (W_ren (wk (S := tN)) (pAll P)) (fst (snd cc)))
                  (tyden_cast (W_ren (wk (S := tN)) (pAll P)) (fst (snd cc)))
                  (snd (fst cc) Wg (snd (snd cc)))
                  (snd (fst cc) Wg (snd (snd cc)))
                  Hρ
                  (EEq_cast (W_ren (wk (S := tN)) (pAll P))
                     (fst (snd cc)) (fst (snd cc)) (proj1 Hc))
                  (proj2 Hw _ _ (EEq_refl_l _ _ _ BWU) _ _ (proj2 Hc))))
                H7) as H8.
    pose proof (eq_trans (eq_sym (dia_all P ρ ρ U U
                  (snd (fst cc) U (snd (snd cc)))
                  (snd (fst cc) U (snd (snd cc)))
                  Hρ BU (proj2 Hw _ _ BU _ _ (proj2 Hc)))) HP) as H9.
    pose proof (proj2 Hw _ _ BWU _ _ (proj2 Hc)) as Hbwd.
    pose proof (eq_trans (eq_sym (dia_EEqE P
                  (fst (snd (fst cc) Wg (snd (snd cc))), ρ)
                  (fst (snd (fst cc) U (snd (snd cc))), ρ)
                  (tyden_cast (W_ren (wk (S := tN)) (pAll P)) (fst (snd cc))
                     (fst (snd (fst cc) Wg (snd (snd cc)))))
                  (U (fst (snd (fst cc) U (snd (snd cc)))))
                  (snd (snd (fst cc) Wg (snd (snd cc))))
                  (snd (snd (fst cc) U (snd (snd cc))))
                  (conj (proj1 Hbwd) Hρ)
                  (triv_EEq (W P) HWt _ _)
                  (proj2 Hbwd))) H8) as H10.
    pose proof (eq_trans (eq_sym H10) H9) as H11.
    discriminate H11.
Qed.

Corollary Valid_r_ip_atomic : forall {Γ} (b b' : tm (tN :: Γ) tBool),
    valid ((pAll (pAtom b) ⊃ pEx (pAtom b'))
           ⊃ pEx (pwk (S := tN) (pAll (pAtom b)) ⊃ pAtom b'))
          (r_ip_atomic b b').
Proof.
  intros Γ b b'; apply Valid_r_ip_generalized; reflexivity.
Qed.

(** ** D2 step 7: soundness of the Dialectica interpretation

    Every derivation in the extended calculus has an extracted realizer that
    wins its Dialectica game: a structural induction on the derivation, each
    case dispatching to the validity lemma of its combinator (which applies to
    [wit] definitionally, thanks to the step-4 refactor). *)

Theorem soundness : forall {Γ} {A : prp Γ} (d : proof Γ A), valid A (wit d).
Proof.
  intros Γ A d; induction d as
    [ Γ
    | Γ P Q u IHu a IHa
    | Γ P Q R u IHu v IHv
    | Γ P
    | Γ P
    | Γ P Q
    | Γ P Q
    | Γ P Q
    | Γ P Q
    | Γ P Q R u IHu
    | Γ P Q R u IHu
    | Γ P Q R u IHu
    | Γ P
    | Γ P Q u IHu
    | Γ Q t
    | Γ Q t
    | Γ P Q u IHu
    | Γ t
    | Γ Q t s
    | Γ t
    | Γ t s
    | Γ Q
    | Γ b b' e d IHd
    | Γ P Hwt Hct
    | Γ P Q Hwt ].
  - exact Valid_tunit_true.
  - exact (Valid_r_mp (wit u) (wit a) IHu IHa).
  - exact (Valid_r_chain (wit u) (wit v) IHu IHv).
  - exact Valid_r_or_contr.
  - exact Valid_r_and_contr.
  - exact Valid_r_or_inl.
  - exact Valid_r_and_eliml.
  - exact Valid_r_or_comm.
  - exact Valid_r_and_comm.
  - exact (Valid_r_or_distr (wit u) IHu).
  - exact (Valid_r_cur (wit u) IHu).
  - exact (Valid_r_uncur (wit u) IHu).
  - exact Valid_r_exfalso.
  - exact (Valid_r_all_intro (wit u) IHu).
  - exact (Valid_r_all_elim t).
  - exact (Valid_r_ex_intro t).
  - exact (Valid_r_ex_elim (wit u) IHu).
  - exact (Valid_teqb_refl t).
  - exact (Valid_r_leibniz t s).
  - exact (Valid_succ_nonzero t).
  - exact (Valid_succ_inj t s).
  - exact (Valid_r_ind Q).
  - exact (Valid_conv e _ IHd).
  - exact (Valid_r_markov_generalized P Hwt Hct).
  - exact (Valid_r_ip_generalized P Q Hwt).
Qed.

(** For closed formulas the environment premise is trivial. *)
Corollary soundness_closed : forall (A : prp []) (d : proof [] A)
    (c : tyden (C A)), EEq (C A) c c ->
    dia A tt (tmden (wit d) tt) c = true.
Proof.
  intros A d c Hc; exact (soundness d tt c I Hc).
Qed.
