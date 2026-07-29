(** * Dialectica: Goedel's functional interpretation of HA into System T

    A "simple" (non-dependent) Dialectica translation of the Heyting
    arithmetic of HA.v into the intrinsically typed System T shared with the
    NbE development:

    - Each formula [A] is assigned System T types [W A] (witnesses / player
      moves) and [C A] (counters / opponent moves).  Because formulas are
      first-order syntax — quantifiers bind number variables, never proposition
      variables — [W A] and [C A] depend only on the propositional skeleton of
      [A], so the translation lands in the *simply typed* System T.  (Contrast
      with theories_old/intuitionistic.v, Bauer's version, where "exotic"
      propositional functions force dependent types.)

    - Each HA proof [d : proof Γ A] is translated to a System T term
      [wit d : tm Γ (W A)].  Since [tm] is intrinsically typed, type
      correctness of the extraction is enforced by construction.

    Design notes:

    - Counters of conjunctions are *products* [C (A ∧ B) = C A × C B] (the
      standard Goedel/A&F choice).  Bauer instead used sums, which System T
      here does not have.  The price is the notorious contraction
      [A ⊃ A ∧ A], whose counter-half must *decide* the matrix [|A|]; the
      matrix is a System T boolean program [diaT A], so the decision happens
      inside the extracted term.

    - Disjunction witnesses use a [tBool] flag instead of a sum type:
      [W (A ∨ B) = tBool × (W A × W B)].

    - Induction is interpreted by primitive recursion (forward) paired with
      Goedel's counterexample *search* (backward), both single [trec]s.

    - The matrix is also given denotationally ([dia] below, via the evaluator
      of Eval.v), yielding the statement of soundness:
      [forall d : proof Γ A, valid A (wit d)].  Proving it needs the usual
      substitution-vs-evaluation lemmas and is left as the next milestone;
      this file is only the *translation*. *)

From Stdlib Require Import List.
Import ListNotations.
From NbE Require Import Syntax OPE Subst.
From SystemT Require Import Terms Eval Semantics HA.

Open Scope ty_scope.
Open Scope tm_scope.
Open Scope prp_scope.

(** ** The type translation

    Witness and counter types, exactly Goedel's:

<<
      A            W A                            C A
      atom         Unit                           Unit
      B ∧ C        W B × W C                      C B × C C
      B ∨ C        Bool × (W B × W C)             C B × C C
      B ⊃ C        (W B ⇒ W C) × (W B ⇒ C C ⇒ C B)   W B × C C
      ∀ B          N ⇒ W B                        N × C B
      ∃ B          N × W B                        C B
>>

    Note [W]/[C] ignore the context: the types depend only on the shape of the
    formula, which is what makes the target *simply* typed System T. *)

Fixpoint W {Γ} (A : prp Γ) : ty :=
  match A with
  | pAtom _ => tUnit
  | pAnd B D => W B × W D
  | pOr B D => tBool × (W B × W D)
  | pImp B D => (W B ⇒ W D) × (W B ⇒ C D ⇒ C B)
  | pAll B => tN ⇒ W B
  | pEx B => tN × W B
  end
with C {Γ} (A : prp Γ) : ty :=
  match A with
  | pAtom _ => tUnit
  | pAnd B D => C B × C D
  | pOr B D => C B × C D
  | pImp B D => W B × C D
  | pAll B => tN × C B
  | pEx B => C B
  end.

(** [W] and [C] are invariant under renaming and substitution — these only
    change the atoms, which contribute [tUnit].  The proofs must stay
    transparent ([Defined]) so that casts along them compute away in the
    extracted examples below. *)

Lemma WC_pren {Γ} (A : prp Γ) :
  forall Δ (o : ope Δ Γ),
    ((W (pren o A) = W A) * (C (pren o A) = C A))%type.
Proof.
  induction A; intros Δ o; simpl.
  - split; reflexivity.
  - destruct (IHA1 Δ o) as [e1 f1]; destruct (IHA2 Δ o) as [e2 f2];
      rewrite e1, f1, e2, f2; split; reflexivity.
  - destruct (IHA1 Δ o) as [e1 f1]; destruct (IHA2 Δ o) as [e2 f2];
      rewrite e1, f1, e2, f2; split; reflexivity.
  - destruct (IHA1 Δ o) as [e1 f1]; destruct (IHA2 Δ o) as [e2 f2];
      rewrite e1, f1, e2, f2; split; reflexivity.
  - destruct (IHA (tN :: Δ) (ope_keep o)) as [e f];
      rewrite e, f; split; reflexivity.
  - destruct (IHA (tN :: Δ) (ope_keep o)) as [e f];
      rewrite e, f; split; reflexivity.
Defined.

Lemma WC_psub {Γ} (A : prp Γ) :
  forall Δ (σ : sub Δ Γ),
    ((W (psub σ A) = W A) * (C (psub σ A) = C A))%type.
Proof.
  induction A; intros Δ σ; simpl.
  - split; reflexivity.
  - destruct (IHA1 Δ σ) as [e1 f1]; destruct (IHA2 Δ σ) as [e2 f2];
      rewrite e1, f1, e2, f2; split; reflexivity.
  - destruct (IHA1 Δ σ) as [e1 f1]; destruct (IHA2 Δ σ) as [e2 f2];
      rewrite e1, f1, e2, f2; split; reflexivity.
  - destruct (IHA1 Δ σ) as [e1 f1]; destruct (IHA2 Δ σ) as [e2 f2];
      rewrite e1, f1, e2, f2; split; reflexivity.
  - destruct (IHA (tN :: Δ) (sub_lift σ)) as [e f];
      rewrite e, f; split; reflexivity.
  - destruct (IHA (tN :: Δ) (sub_lift σ)) as [e f];
      rewrite e, f; split; reflexivity.
Defined.

Definition W_ren {Δ Γ} (o : ope Δ Γ) (A : prp Γ) : W (pren o A) = W A :=
  fst (WC_pren A Δ o).
Definition C_ren {Δ Γ} (o : ope Δ Γ) (A : prp Γ) : C (pren o A) = C A :=
  snd (WC_pren A Δ o).
Definition W_sub {Δ Γ} (σ : sub Δ Γ) (A : prp Γ) : W (psub σ A) = W A :=
  fst (WC_psub A Δ σ).
Definition C_sub {Δ Γ} (σ : sub Δ Γ) (A : prp Γ) : C (psub σ A) = C A :=
  snd (WC_psub A Δ σ).

(** ** The matrix, internally

    [diaT A : W A ⇒ C A ⇒ Bool] is the quantifier-free matrix [|A|(w, c)] of
    the interpretation — and since atoms are decidable it is *itself a System T
    program*.  This is essential: the realizers of contraction ([A ⊃ A ∧ A])
    and of induction must run this test at evaluation time. *)

Fixpoint diaT {Γ} (A : prp Γ) : tm Γ (W A ⇒ C A ⇒ tBool) :=
  match A as a in prp Γ0 return tm Γ0 (W a ⇒ C a ⇒ tBool) with
  | pAtom b => tlam (tlam (wk1 (wk1 b)))
  | pAnd B D =>
      (* |B|(w.1, c.1) && |D|(w.2, c.2) *)
      tlam (tlam (tandb (wk1 (wk1 (diaT B)) · tfst v1 · tfst v0)
                        (wk1 (wk1 (diaT D)) · tsnd v1 · tsnd v0)))
  | pOr B D =>
      (* if flag then |B|(w.2.1, c.1) else |D|(w.2.2, c.2) *)
      tlam (tlam (tif (tfst v1)
                      (wk1 (wk1 (diaT B)) · tfst (tsnd v1) · tfst v0)
                      (wk1 (wk1 (diaT D)) · tsnd (tsnd v1) · tsnd v0)))
  | pImp B D =>
      (* |B|(c.1, w.2 c.1 c.2) ⟹ |D|(w.1 c.1, c.2) *)
      tlam (tlam (timplb (wk1 (wk1 (diaT B)) · tfst v0 · (tsnd v1 · tfst v0 · tsnd v0))
                         (wk1 (wk1 (diaT D)) · (tfst v1 · tfst v0) · tsnd v0)))
  | pAll B =>
      (* |B[x := c.1]|(w (c.1), c.2) *)
      tlam (tlam (subst (sub_at0 wkn2 (tfst v0)) (diaT B)
                    · (v1 · tfst v0) · tsnd v0))
  | pEx B =>
      (* |B[x := w.1]|(w.2, c) *)
      tlam (tlam (subst (sub_at0 wkn2 (tfst v1)) (diaT B)
                    · tsnd v1 · v0))
  end.

(** ** The proof translation

    [wit d : tm Γ (W A)] is the Dialectica realizer extracted from [d].  A
    witness of an implication is a *pair*: the forward map on witnesses and
    the backward map on counters, so each axiom below is a small System T
    program (they are the de Bruijn renderings of the programs in Bauer's
    [Theorem]s, adapted to product counters for [∧]).

    Free number variables of [A] are just term variables of type [tN] in [Γ],
    so no closure/abstraction is needed: axioms mentioning arbitrary numeric
    terms [t] simply embed (weakenings of) [t]. *)

Fixpoint wit {Γ} {P : prp Γ} (d : proof Γ P) : tm Γ (W P) :=
  match d in proof Γ0 P0 return tm Γ0 (W P0) with
  | ax_true => tunit

  | @ax_mp _ _ _ u a => tfst (wit u) · wit a

  (* λw. v.1 (u.1 w) , λw c. u.2 w (v.2 (u.1 w) c) *)
  | @ax_chain _ _ _ _ u v =>
      tpair (tlam (tfst (wk1 (wit v)) · (tfst (wk1 (wit u)) · v0)))
            (tlam (tlam (tsnd (wk1 (wk1 (wit u))) · v1 ·
                           (tsnd (wk1 (wk1 (wit v))) · (tfst (wk1 (wk1 (wit u))) · v1) · v0))))

  (* λw. if w.1 then w.2.1 else w.2.2 , λw c. (c, c) *)
  | @ax_or_contr _ _ =>
      tpair (tlam (tif (tfst v0) (tfst (tsnd v0)) (tsnd (tsnd v0))))
            (tlam (tlam (tpair v0 v0)))

  (* λw. (w, w) , λw c. if |P|(w, c.1) then c.2 else c.1
     — the contraction that needs the internal decision [diaT]. *)
  | @ax_and_contr _ P1 =>
      tpair (tlam (tpair v0 v0))
            (tlam (tlam (tif (wk1 (wk1 (diaT P1)) · v1 · tfst v0)
                             (tsnd v0) (tfst v0))))

  (* λw. (true, (w, dummy)) , λw c. c.1 *)
  | @ax_or_inl _ _ Q1 =>
      tpair (tlam (tpair ttrue (tpair v0 (tdefault (W Q1)))))
            (tlam (tlam (tfst v0)))

  (* λw. w.1 , λw c. (c, dummy) *)
  | @ax_and_eliml _ _ Q1 =>
      tpair (tlam (tfst v0))
            (tlam (tlam (tpair v0 (tdefault (C Q1)))))

  (* λw. (¬w.1, (w.2.2, w.2.1)) , λw c. (c.2, c.1) *)
  | @ax_or_comm _ _ _ =>
      tpair (tlam (tpair (tnegb (tfst v0)) (tpair (tsnd (tsnd v0)) (tfst (tsnd v0)))))
            (tlam (tlam (tpair (tsnd v0) (tfst v0))))

  | @ax_and_comm _ _ _ =>
      tpair (tlam (tpair (tsnd v0) (tfst v0)))
            (tlam (tlam (tpair (tsnd v0) (tfst v0))))

  (* λw. (w.1, (w.2.1, u.1 w.2.2)) , λw c. (c.1, u.2 w.2.2 c.2) *)
  | @ax_or_distr _ _ _ _ u =>
      tpair (tlam (tpair (tfst v0)
                         (tpair (tfst (tsnd v0)) (tfst (wk1 (wit u)) · tsnd (tsnd v0)))))
            (tlam (tlam (tpair (tfst v0)
                               (tsnd (wk1 (wk1 (wit u))) · tsnd (tsnd v1) · tsnd v0))))

  (* λp. ( λq. u.1 (p,q) , λq c. (u.2 (p,q) c).2 ) , λp qc. (u.2 (p, qc.1) qc.2).1 *)
  | @ax_cur _ _ _ _ u =>
      tpair (tlam (tpair
               (tlam (tfst (wk1 (wk1 (wit u))) · tpair v1 v0))
               (tlam (tlam (tsnd (tsnd (wk1 (wk1 (wk1 (wit u)))) · tpair v2 v1 · v0))))))
            (tlam (tlam (tfst (tsnd (wk1 (wk1 (wit u))) · tpair v1 (tfst v0) · tsnd v0))))

  (* λw. (u.1 w.1).1 w.2 ,
     λw c. ( u.2 w.1 (w.2, c) , (u.1 w.1).2 w.2 c ) *)
  | @ax_uncur _ _ _ _ u =>
      tpair (tlam (tfst (tfst (wk1 (wit u)) · tfst v0) · tsnd v0))
            (tlam (tlam (tpair
               (tsnd (wk1 (wk1 (wit u))) · tfst v1 · tpair (tsnd v1) v0)
               (tsnd (tfst (wk1 (wk1 (wit u))) · tfst v1) · tsnd v1 · v0))))

  | @ax_exfalso _ P1 =>
      tpair (tlam (tdefault (W P1)))
            (tlam (tlam tunit))

  (* u : tm (tN :: Γ) (W (pwk P ⊃ Q));  the extra variable is the ∀-bound one.
     f = λw n. (u[x:=n]).1 w   g = λw (n,c). (u[x:=n]).2 w c *)
  | @ax_all_intro _ P1 Q1 u =>
      let eW := W_ren wk P1 in
      let eC := C_ren wk P1 in
      tpair (tlam (tlam
               (tfst (subst (sub_at0 wkn2 v0) (wit u))
                  · tcast (eq_sym eW) v1)))
            (tlam (tlam (tcast eC
               (tsnd (subst (sub_at0 wkn2 (tfst v0)) (wit u))
                  · tcast (eq_sym eW) v1 · tsnd v0))))

  (* f = λw. w t   g = λw c. (t, c) *)
  | @ax_all_elim _ Q1 t =>
      let eW := W_sub (sub1 t) Q1 in
      let eC := C_sub (sub1 t) Q1 in
      tpair (tlam (tcast (eq_sym eW) (v0 · wk1 t)))
            (tlam (tlam (tpair (wk1 (wk1 t)) (tcast eC v0))))

  (* f = λw. (t, w)   g = λw c. c *)
  | @ax_ex_intro _ Q1 t =>
      let eW := W_sub (sub1 t) Q1 in
      let eC := C_sub (sub1 t) Q1 in
      tpair (tlam (tpair (wk1 t) (tcast eW v0)))
            (tlam (tlam (tcast (eq_sym eC) v0)))

  (* u : tm (tN :: Γ) (W (Q ⊃ pwk P)).
     f = λ(n,w). (u[x:=n]).1 w   g = λ(n,w) c. (u[x:=n]).2 w c *)
  | @ax_ex_elim _ P1 Q1 u =>
      let eW := W_ren wk P1 in
      let eC := C_ren wk P1 in
      tpair (tlam (tcast eW
               (tfst (subst (sub_at0 wk (tfst v0)) (wit u)) · tsnd v0)))
            (tlam (tlam
               (tsnd (subst (sub_at0 wkn2 (tfst v1)) (wit u))
                  · tsnd v1 · tcast (eq_sym eC) v0)))

  | ax_eq_refl _ => tunit

  (* All atoms have trivial witnesses, so Leibniz is transport:
     λ_. ( λw. w , λw c. c ) , λ_ c. tt *)
  | @ax_leibniz _ Q1 t s =>
      let eWt := W_sub (sub1 t) Q1 in
      let eWs := W_sub (sub1 s) Q1 in
      let eCt := C_sub (sub1 t) Q1 in
      let eCs := C_sub (sub1 s) Q1 in
      tpair (tlam (tpair
               (tlam (tcast (eq_trans eWt (eq_sym eWs)) v0))
               (tlam (tlam (tcast (eq_trans eCs (eq_sym eCt)) v0)))))
            (tlam (tlam tunit))

  | ax_succ_nonzero _ =>
      tpair (tlam tunit) (tlam (tlam tunit))

  | ax_succ_inj _ _ =>
      tpair (tlam tunit) (tlam (tlam tunit))

  (* Induction.  Write the premise p = (z, s) with
       z : W Q[0]                                    (base witness)
       s : N ⇒ (W Q ⇒ W Q[S x]) × (W Q ⇒ C Q[S x] ⇒ C Q)   (step witness)
     Forward: λp n. rec z (λk r. (p.2 k).1 r) n — primitive recursion.
     Backward: given a counter (n, c) against [∀x.Q], search downward from n
     for a failing step (Goedel's / Bauer's [search]): recursion computes the
     pair (w_k, g_k) where w_k realizes Q[k] and
       g_0     c = (c, dummy)
       g_(k+1) c = let c' = (p.2 k).2 w_k c in
                   if |Q[k]|(w_k, c') then (dummy, (k, (w_k, c))) else g_k c'
     returning a counter against the premise conjunction. *)
  | @ax_ind Γ0 Q1 =>
      let eW0 := W_sub (sub1 tzero) Q1 in
      let eC0 := C_sub (sub1 tzero) Q1 in
      let eWS := W_sub sub_succ Q1 in
      let eCS := C_sub sub_succ Q1 in
      tpair
        (tlam (tlam (trec (tcast eW0 (tfst v1))
                          (tlam (tlam (tcast eWS (tfst (tsnd v3 · v1) · v0))))
                          v0)))
        (tlam (tlam
          (tsnd (trec
             (* (w_0, g_0) *)
             (tpair (tcast eW0 (tfst v1))
                    (tlam (tpair (tcast (eq_sym eC0) v0)
                                 (tpair tzero
                                        (tpair (tdefault (W Q1))
                                               (tdefault (C (psucc Q1))))))))
             (* λk (w_k, g_k). (w_(k+1), g_(k+1)) *)
             (tlam (tlam (tpair
                (tcast eWS (tfst (tsnd v3 · v1) · tfst v0))
                (tlam
                   (let cS := tcast (eq_sym eCS) v0 in
                    let c' := tsnd (tsnd v4 · v2) · tfst v1 · cS in
                    tif (subst (sub_at0 wkn5 v2) (diaT Q1)
                           · tfst v1 · c')
                        (tpair (tdefault (C (psub1 Q1 tzero)))
                               (tpair v2 (tpair (tfst v1) cS)))
                        (tsnd v1 · c'))))))
             (tfst v0))
           · tsnd v0)))
  end.

(** ** Validity

    The Dialectica matrix, denotationally (via Eval.v), and the interpretation
    proper: [A] is valid when some System T witness [t] beats every counter.

    Quantification is over the PER *domain* — self-related environments and
    counters — not over arbitrary values.  Under the axiom-free PER
    discipline (Semantics.v) this restriction is forced: the commutation
    lemmas soundness relies on only speak about values in the domain, and an
    unrestricted statement would be false — e.g. it would make every
    [F : (nat -> nat) -> nat] respect pointwise equality of its argument,
    which is exactly the extensionality we do not assume.  ([diaT] itself
    substitutes internally at quantifiers, so even reaching the boolean
    observation passes through higher-order values first.)

    The restriction is cheap where it matters:
    - closed formulas ([Γ = []]): the environment premise is trivial;
    - pure HA contexts (all [tN]): environments are tuples of numbers,
      self-related for free;
    - the witness side needs no premise: [tmden t ρ] is self-related by the
      fundamental lemma (D2 step 2) whenever [ρ] is. *)

Definition dia {Γ} (A : prp Γ) (ρ : cxtden Γ)
  (w : tyden (W A)) (c : tyden (C A)) : bool :=
  tmden (diaT A) ρ w c.

Definition valid {Γ} (A : prp Γ) (t : tm Γ (W A)) : Prop :=
  forall ρ c, EEqE Γ ρ ρ -> EEq (C A) c c ->
    dia A ρ (tmden t ρ) c = true.

(** Soundness — the statement this translation is aiming at:

      [forall Γ (A : prp Γ) (d : proof Γ A), valid A (wit d)]

    Proving it is the natural next milestone; it needs the usual commutation
    lemmas between [tm_ren]/[subst] and [tmden] (and their consequences for
    [diaT] under [pren]/[psub]), after which each axiom's verification is the
    corresponding [Theorem] of theories_old/intuitionistic.v. *)

(** ** Examples *)

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

(** Validity of the two examples — instances of the (yet unproven) general
    soundness theorem, checked by computation. *)

Example ex_two_valid : valid _ (wit ex_two).
Proof. intros ρ c _ _; destruct ρ, c; reflexivity. Qed.

Example ex_succ_valid : valid _ (wit ex_succ).
Proof.
  intros ρ c _ _; destruct ρ; destruct c as [n u]; destruct u.
  exact (teqb_refl (Γ := []) tt (S n)).
Qed.

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
