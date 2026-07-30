(** * Dialectica: functional interpretation of arithmetic into System T

    A "simple" (non-dependent) Dialectica translation of the Heyting
    arithmetic fragment of HA.v, extended with its D3 characteristic
    principles, into the intrinsically typed System T shared with the NbE
    development:

    - Each formula [A] is assigned System T types [W A] (witnesses / player
      moves) and [C A] (counters / opponent moves).  Because formulas are
      first-order syntax — quantifiers bind number variables, never proposition
      variables — [W A] and [C A] depend only on the propositional skeleton of
      [A], so the translation lands in the *simply typed* System T.  (Contrast
      with theories_old/intuitionistic.v, Bauer's version, where "exotic"
      propositional functions force dependent types.)

    - Each derivation [d : proof Γ A] in the extended calculus is translated
      to a System T term
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

    - [Validity.v] gives [diaT] a denotational reading [dia], defines
      validity, and proves the axiom-free soundness theorem
      [forall d : proof Γ A, valid A (wit d)].  This file contains only the
      syntactic/computational translation. *)

From Stdlib Require Import List.
Import ListNotations.
From NbE Require Import Syntax OPE Subst.
From SystemT Require Import Terms HA.

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
    extracted examples in [Examples.v]. *)

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
      tlam (tlam (subst (sub_at0 (drop_prefix [_; _]) (tfst v0)) (diaT B)
                    · (v1 · tfst v0) · tsnd v0))
  | pEx B =>
      (* |B[x := w.1]|(w.2, c) *)
      tlam (tlam (subst (sub_at0 (drop_prefix [_; _]) (tfst v1)) (diaT B)
                    · tsnd v1 · v0))
  end.

(** ** The realizer combinators

    One named System T program per proof rule (they are the de Bruijn
    renderings of the programs in Bauer's [Theorem]s, adapted to product
    counters for [∧]).  A witness of an implication is a *pair*: the forward
    map on witnesses and the backward map on counters.  Rules with premises
    take the premise realizers as term arguments.

    [wit] below dispatches to these, so a validity lemma about [r_foo]
    applies to [wit (ax_foo ...)] definitionally — the shape step 6 needs
    (the combinator-plus-lemma organization of theories_old/linear.v).

    Free number variables of the formulas are just term variables of type
    [tN] in [Γ], so no closure/abstraction is needed: combinators mentioning
    arbitrary numeric terms [t] simply embed (weakenings of) [t]. *)

(* λw. u.1 w — modus ponens is application of the forward map. *)
Definition r_mp {Γ} {P Q : prp Γ}
  (u : tm Γ (W (P ⊃ Q))) (a : tm Γ (W P)) : tm Γ (W Q) :=
  tfst u · a.

(* λw. v.1 (u.1 w) , λw c. u.2 w (v.2 (u.1 w) c) *)
Definition r_chain {Γ} {P Q R : prp Γ}
  (u : tm Γ (W (P ⊃ Q))) (v : tm Γ (W (Q ⊃ R))) : tm Γ (W (P ⊃ R)) :=
  tpair (tlam (tfst (wk1 v) · (tfst (wk1 u) · v0)))
        (tlam (tlam (tsnd (wk1 (wk1 u)) · v1 ·
                       (tsnd (wk1 (wk1 v)) · (tfst (wk1 (wk1 u)) · v1) · v0)))).

(* λw. if w.1 then w.2.1 else w.2.2 , λw c. (c, c) *)
Definition r_or_contr {Γ} {P : prp Γ} : tm Γ (W (P ∨ P ⊃ P)) :=
  tpair (tlam (tif (tfst v0) (tfst (tsnd v0)) (tsnd (tsnd v0))))
        (tlam (tlam (tpair v0 v0))).

(* λw. (w, w) , λw c. if |P|(w, c.1) then c.2 else c.1
   — the contraction that needs the internal decision [diaT]. *)
Definition r_and_contr {Γ} {P : prp Γ} : tm Γ (W (P ⊃ P ∧ P)) :=
  tpair (tlam (tpair v0 v0))
        (tlam (tlam (tif (wk1 (wk1 (diaT P)) · v1 · tfst v0)
                         (tsnd v0) (tfst v0)))).

(* λw. (true, (w, dummy)) , λw c. c.1 *)
Definition r_or_inl {Γ} {P Q : prp Γ} : tm Γ (W (P ⊃ P ∨ Q)) :=
  tpair (tlam (tpair ttrue (tpair v0 (tdefault (W Q)))))
        (tlam (tlam (tfst v0))).

(* λw. w.1 , λw c. (c, dummy) *)
Definition r_and_eliml {Γ} {P Q : prp Γ} : tm Γ (W (P ∧ Q ⊃ P)) :=
  tpair (tlam (tfst v0))
        (tlam (tlam (tpair v0 (tdefault (C Q))))).

(* λw. (¬w.1, (w.2.2, w.2.1)) , λw c. (c.2, c.1) *)
Definition r_or_comm {Γ} {P Q : prp Γ} : tm Γ (W (P ∨ Q ⊃ Q ∨ P)) :=
  tpair (tlam (tpair (tnegb (tfst v0))
                     (tpair (tsnd (tsnd v0)) (tfst (tsnd v0)))))
        (tlam (tlam (tpair (tsnd v0) (tfst v0)))).

Definition r_and_comm {Γ} {P Q : prp Γ} : tm Γ (W (P ∧ Q ⊃ Q ∧ P)) :=
  tpair (tlam (tpair (tsnd v0) (tfst v0)))
        (tlam (tlam (tpair (tsnd v0) (tfst v0)))).

(* λw. (w.1, (w.2.1, u.1 w.2.2)) , λw c. (c.1, u.2 w.2.2 c.2) *)
Definition r_or_distr {Γ} {P Q R : prp Γ}
  (u : tm Γ (W (P ⊃ Q))) : tm Γ (W (R ∨ P ⊃ R ∨ Q)) :=
  tpair (tlam (tpair (tfst v0)
                     (tpair (tfst (tsnd v0)) (tfst (wk1 u) · tsnd (tsnd v0)))))
        (tlam (tlam (tpair (tfst v0)
                           (tsnd (wk1 (wk1 u)) · tsnd (tsnd v1) · tsnd v0))))
.

(* λp. ( λq. u.1 (p,q) , λq c. (u.2 (p,q) c).2 ) , λp qc. (u.2 (p, qc.1) qc.2).1 *)
Definition r_cur {Γ} {P Q R : prp Γ}
  (u : tm Γ (W (P ∧ Q ⊃ R))) : tm Γ (W (P ⊃ (Q ⊃ R))) :=
  tpair (tlam (tpair
           (tlam (tfst (wk1 (wk1 u)) · tpair v1 v0))
           (tlam (tlam (tsnd (tsnd (wk1 (wk1 (wk1 u))) · tpair v2 v1 · v0))))))
        (tlam (tlam (tfst (tsnd (wk1 (wk1 u)) · tpair v1 (tfst v0) · tsnd v0)))).

(* λw. (u.1 w.1).1 w.2 ,
   λw c. ( u.2 w.1 (w.2, c) , (u.1 w.1).2 w.2 c ) *)
Definition r_uncur {Γ} {P Q R : prp Γ}
  (u : tm Γ (W (P ⊃ (Q ⊃ R)))) : tm Γ (W (P ∧ Q ⊃ R)) :=
  tpair (tlam (tfst (tfst (wk1 u) · tfst v0) · tsnd v0))
        (tlam (tlam (tpair
           (tsnd (wk1 (wk1 u)) · tfst v1 · tpair (tsnd v1) v0)
           (tsnd (tfst (wk1 (wk1 u)) · tfst v1) · tsnd v1 · v0)))).

Definition r_exfalso {Γ} {P : prp Γ} : tm Γ (W (pFalse ⊃ P)) :=
  tpair (tlam (tdefault (W P)))
        (tlam (tlam tunit)).

(* u : tm (tN :: Γ) (W (pwk P ⊃ Q));  the extra variable is the ∀-bound one.
   f = λw n. (u[x:=n]).1 w   g = λw (n,c). (u[x:=n]).2 w c *)
Definition r_all_intro {Γ} {P : prp Γ} {Q : prp (tN :: Γ)}
  (u : tm (tN :: Γ) (W (pwk P ⊃ Q))) : tm Γ (W (P ⊃ pAll Q)) :=
  let eW := W_ren wk P in
  let eC := C_ren wk P in
  tpair (tlam (tlam
           (tfst (subst (sub_at0 (drop_prefix [_; _]) v0) u)
              · tcast (eq_sym eW) v1)))
        (tlam (tlam (tcast eC
           (tsnd (subst (sub_at0 (drop_prefix [_; _]) (tfst v0)) u)
              · tcast (eq_sym eW) v1 · tsnd v0)))).

(* f = λw. w t   g = λw c. (t, c) *)
Definition r_all_elim {Γ} {Q : prp (tN :: Γ)} (t : tm Γ tN) :
  tm Γ (W (pAll Q ⊃ psub1 Q t)) :=
  let eW := W_sub (scons t) Q in
  let eC := C_sub (scons t) Q in
  tpair (tlam (tcast (eq_sym eW) (v0 · wk1 t)))
        (tlam (tlam (tpair (wk1 (wk1 t)) (tcast eC v0)))).

(* f = λw. (t, w)   g = λw c. c *)
Definition r_ex_intro {Γ} {Q : prp (tN :: Γ)} (t : tm Γ tN) :
  tm Γ (W (psub1 Q t ⊃ pEx Q)) :=
  let eW := W_sub (scons t) Q in
  let eC := C_sub (scons t) Q in
  tpair (tlam (tpair (wk1 t) (tcast eW v0)))
        (tlam (tlam (tcast (eq_sym eC) v0))).

(* u : tm (tN :: Γ) (W (Q ⊃ pwk P)).
   f = λ(n,w). (u[x:=n]).1 w   g = λ(n,w) c. (u[x:=n]).2 w c *)
Definition r_ex_elim {Γ} {P : prp Γ} {Q : prp (tN :: Γ)}
  (u : tm (tN :: Γ) (W (Q ⊃ pwk P))) : tm Γ (W (pEx Q ⊃ P)) :=
  let eW := W_ren wk P in
  let eC := C_ren wk P in
  tpair (tlam (tcast eW
           (tfst (subst (sub_at0 wk (tfst v0)) u) · tsnd v0)))
        (tlam (tlam
           (tsnd (subst (sub_at0 (drop_prefix [_; _]) (tfst v1)) u)
              · tsnd v1 · tcast (eq_sym eC) v0))).

(* All atoms have trivial witnesses, so Leibniz is transport:
   λ_. ( λw. w , λw c. c ) , λ_ c. tt *)
Definition r_leibniz {Γ} {Q : prp (tN :: Γ)} (t s : tm Γ tN) :
  tm Γ (W (pEq t s ⊃ (psub1 Q t ⊃ psub1 Q s))) :=
  let eWt := W_sub (scons t) Q in
  let eWs := W_sub (scons s) Q in
  let eCt := C_sub (scons t) Q in
  let eCs := C_sub (scons s) Q in
  tpair (tlam (tpair
           (tlam (tcast (eq_trans eWt (eq_sym eWs)) v0))
           (tlam (tlam (tcast (eq_trans eCs (eq_sym eCt)) v0)))))
        (tlam (tlam tunit)).

(* An implication between atoms has purely administrative realizers (all
   moves are units) — covers the successor axioms. *)
Definition r_atom_imp {Γ} {b b' : tm Γ tBool} :
  tm Γ (W (pAtom b ⊃ pAtom b')) :=
  tpair (tlam tunit) (tlam (tlam tunit)).

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
Definition r_ind {Γ} {Q : prp (tN :: Γ)} :
  tm Γ (W ((psub1 Q tzero ∧ pAll (Q ⊃ psucc Q)) ⊃ pAll Q)) :=
  let eW0 := W_sub (scons tzero) Q in
  let eC0 := C_sub (scons tzero) Q in
  let eWS := W_sub sub_succ Q in
  let eCS := C_sub sub_succ Q in
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
                                    (tpair (tdefault (W Q))
                                           (tdefault (C (psucc Q))))))))
         (* λk (w_k, g_k). (w_(k+1), g_(k+1)) *)
         (tlam (tlam (tpair
            (tcast eWS (tfst (tsnd v3 · v1) · tfst v0))
            (tlam
               (let cS := tcast (eq_sym eCS) v0 in
                let c' := tsnd (tsnd v4 · v2) · tfst v1 · cS in
                tif (subst (sub_at0 (drop_prefix [_; _; _; _; _]) v2) (diaT Q)
                       · tfst v1 · c')
                    (tpair (tdefault (C (psub1 Q tzero)))
                           (tpair v2 (tpair (tfst v1) cS)))
                    (tsnd v1 · c'))))))
         (tfst v0))
       · tsnd v0))).

(* Markov: from a witness h of ¬∀x.¬P(x), the counter-half of h applied to
   the canonical [tdefault] ∀-family yields the existential index; the
   existential's [W P]-component and the backward map are canonical moves —
   witness/counter triviality of [P] (the side conditions on [ax_markov])
   makes them as good as any.  (Bauer's [markov_generalized] realizer.) *)
Definition r_markov {Γ} (P : prp (tN :: Γ)) :
  tm Γ (W (pNot (pAll (pNot P)) ⊃ pEx P)) :=
  tpair
    (tlam (tpair
       (tfst (tsnd v0 · tdefault (W (pAll (pNot P))) · tunit))
       (tdefault (W P))))
    (tlam (tlam (tpair (tdefault (W (pAll (pNot P)))) tunit))).

(* Independence of Premise: from a witness a of (∀x.P(x)) ⊃ ∃y.Q(y), the
   forward map of a at the canonical ∀-family yields the existential index
   and (projected) the [Q]-witness; the inner backward map returns a's
   counter at the canonical family (one [tcast], since [pwk] of a general
   formula only computes up to the invariance lemmas); the outer backward
   map threads the [Q]-counter through.  (Bauer's [ip_generalized]
   realizer; no condition on [Q] is needed here because our [∃]-counters
   are non-dependent.) *)
Definition r_ip {Γ} (P Q : prp (tN :: Γ)) :
  tm Γ (W ((pAll P ⊃ pEx Q) ⊃ pEx (pwk (pAll P) ⊃ Q))) :=
  tpair
    (tlam (tpair
       (tfst (tfst v0 · tdefault (W (pAll P))))
       (tpair
          (tlam (tsnd (tfst v1 · tdefault (W (pAll P)))))
          (tlam (tlam (tcast (eq_sym (C_ren wk (pAll P)))
                         (tsnd v2 · tdefault (W (pAll P)) · v0)))))))
    (tlam (tlam (tpair (tdefault (W (pAll P))) (tsnd v0)))).

(** Atomic compatibility wrappers for the original D3 realizers. *)
Definition r_markov_atomic {Γ} (b : tm (tN :: Γ) tBool) :
    tm Γ (W (pNot (pAll (pNot (pAtom b))) ⊃ pEx (pAtom b))) :=
  r_markov (pAtom b).

Definition r_ip_atomic {Γ} (b b' : tm (tN :: Γ) tBool) :
    tm Γ (W ((pAll (pAtom b) ⊃ pEx (pAtom b'))
             ⊃ pEx (pwk (pAll (pAtom b)) ⊃ pAtom b'))) :=
  r_ip (pAtom b) (pAtom b').

(** ** The proof translation

    [wit d : tm Γ (W A)] dispatches each proof rule to its realizer
    combinator.  Since [tm] is intrinsically typed, type correctness of the
    whole translation is enforced by construction. *)

Fixpoint wit {Γ} {P : prp Γ} (d : proof Γ P) : tm Γ (W P) :=
  match d in proof Γ0 P0 return tm Γ0 (W P0) with
  | ax_true => tunit
  | @ax_mp _ _ _ u a => r_mp (wit u) (wit a)
  | @ax_chain _ _ _ _ u v => r_chain (wit u) (wit v)
  | @ax_or_contr _ _ => r_or_contr
  | @ax_and_contr _ _ => r_and_contr
  | @ax_or_inl _ _ _ => r_or_inl
  | @ax_and_eliml _ _ _ => r_and_eliml
  | @ax_or_comm _ _ _ => r_or_comm
  | @ax_and_comm _ _ _ => r_and_comm
  | @ax_or_distr _ _ _ _ u => r_or_distr (wit u)
  | @ax_cur _ _ _ _ u => r_cur (wit u)
  | @ax_uncur _ _ _ _ u => r_uncur (wit u)
  | @ax_exfalso _ _ => r_exfalso
  | @ax_all_intro _ _ _ u => r_all_intro (wit u)
  | @ax_all_elim _ _ t => r_all_elim t
  | @ax_ex_intro _ _ t => r_ex_intro t
  | @ax_ex_elim _ _ _ u => r_ex_elim (wit u)
  | ax_eq_refl _ => tunit
  | @ax_leibniz _ _ t s => r_leibniz t s
  | ax_succ_nonzero _ => r_atom_imp
  | ax_succ_inj _ _ => r_atom_imp
  | @ax_ind _ _ => r_ind
  | ax_conv _ d0 => wit d0
  | ax_markov P _ _ => r_markov P
  | ax_ip P Q _ => r_ip P Q
  end.
