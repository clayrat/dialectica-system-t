(** * HA: Heyting arithmetic over System T terms

    First-order intuitionistic arithmetic, independent of any interpretation:
    formulas, formula renaming/substitution, and a Hilbert-style proof
    calculus.  Dialectica.v interprets this logic; other interpretations
    (modified realizability, Diller–Nahm, a linear decomposition) would import
    this same file.

    ** Formulas

    [prp Γ] are first-order arithmetic formulas with free variables in [Γ]
    (for "pure" HA take [Γ] to consist of [tN] entries only).  Quantifiers
    bind a fresh [tN] variable, de Bruijn style.  Atoms are arbitrary boolean
    System T terms, which covers [t ≐ s], [t ≤ s], primality, ... — any
    primitive recursive predicate — while staying decidable, as the basic
    Dialectica interpretation requires. *)

From Stdlib Require Import List.
Import ListNotations.
From NbE Require Import Syntax OPE Subst.
From SystemT Require Import Terms.

Open Scope ty_scope.
Open Scope tm_scope.

Inductive prp : cxt -> Type :=
| pAtom : forall {Γ}, tm Γ tBool -> prp Γ
| pAnd  : forall {Γ}, prp Γ -> prp Γ -> prp Γ
| pOr   : forall {Γ}, prp Γ -> prp Γ -> prp Γ
| pImp  : forall {Γ}, prp Γ -> prp Γ -> prp Γ
| pAll  : forall {Γ}, prp (tN :: Γ) -> prp Γ
| pEx   : forall {Γ}, prp (tN :: Γ) -> prp Γ.

Declare Scope prp_scope.
Infix "∧" := pAnd (at level 74, left associativity) : prp_scope.
Infix "∨" := pOr (at level 76, left associativity) : prp_scope.
Infix "⊃" := pImp (at level 78, right associativity) : prp_scope.
Open Scope prp_scope.

Definition pTrue {Γ} : prp Γ := pAtom ttrue.
Definition pFalse {Γ} : prp Γ := pAtom tfalse.
Definition pNot {Γ} (A : prp Γ) : prp Γ := A ⊃ pFalse.
Definition pEq {Γ} (t s : tm Γ tN) : prp Γ := pAtom (teqb · t · s).

(** ** Renaming and substitution

    They lift pointwise to formulas (they only touch the atoms, going under
    one [tN] binder at each quantifier). *)

Fixpoint pren_ {Γ} (A : prp Γ) : forall Δ, ope Δ Γ -> prp Δ :=
  match A in prp Γ0 return forall Δ, ope Δ Γ0 -> prp Δ with
  | pAtom b => fun Δ o => pAtom (tm_ren o b)
  | pAnd A1 A2 => fun Δ o => pAnd (pren_ A1 Δ o) (pren_ A2 Δ o)
  | pOr A1 A2 => fun Δ o => pOr (pren_ A1 Δ o) (pren_ A2 Δ o)
  | pImp A1 A2 => fun Δ o => pImp (pren_ A1 Δ o) (pren_ A2 Δ o)
  | pAll A1 => fun Δ o => pAll (pren_ A1 _ (ope_keep o))
  | pEx A1 => fun Δ o => pEx (pren_ A1 _ (ope_keep o))
  end.

Definition pren {Δ Γ} (o : ope Δ Γ) (A : prp Γ) : prp Δ := pren_ A Δ o.

Fixpoint psub_ {Γ} (A : prp Γ) : forall Δ, sub Δ Γ -> prp Δ :=
  match A in prp Γ0 return forall Δ, sub Δ Γ0 -> prp Δ with
  | pAtom b => fun Δ σ => pAtom (subst σ b)
  | pAnd A1 A2 => fun Δ σ => pAnd (psub_ A1 Δ σ) (psub_ A2 Δ σ)
  | pOr A1 A2 => fun Δ σ => pOr (psub_ A1 Δ σ) (psub_ A2 Δ σ)
  | pImp A1 A2 => fun Δ σ => pImp (psub_ A1 Δ σ) (psub_ A2 Δ σ)
  | pAll A1 => fun Δ σ => pAll (psub_ A1 _ (sub_lift σ))
  | pEx A1 => fun Δ σ => pEx (psub_ A1 _ (sub_lift σ))
  end.

Definition psub {Δ Γ} (σ : sub Δ Γ) (A : prp Γ) : prp Δ := psub_ A Δ σ.

(** Weakening a formula (used where A&F have a freshness side condition). *)
Definition pwk {Γ S} (A : prp Γ) : prp (S :: Γ) := pren wk A.

(** Instantiating the outermost quantified variable at a numeric term. *)
Definition psub1 {Γ} (A : prp (tN :: Γ)) (t : tm Γ tN) : prp Γ :=
  psub (sub1 t) A.

(** [A(x)] ↦ [A(S x)] (via [sub_succ] from Terms.v): needed to state
    induction. *)
Definition psucc {Γ} (A : prp (tN :: Γ)) : prp (tN :: Γ) := psub sub_succ A.

(** ** Proofs

    A Hilbert-style calculus for intuitionistic first-order arithmetic,
    following the axiomatization Bauer verified semantically in
    theories_old/intuitionistic.v (i.e. Avigad & Feferman's), plus the usual
    HA axioms: equality, successor, induction.  Quantifier side conditions
    ("x not free in ...") are expressed by explicit weakening [pwk]. *)

Inductive proof : forall Γ : cxt, prp Γ -> Type :=
| ax_true : forall {Γ}, proof Γ pTrue
| ax_mp : forall {Γ} {P Q : prp Γ},
    proof Γ (P ⊃ Q) -> proof Γ P -> proof Γ Q
| ax_chain : forall {Γ} {P Q R : prp Γ},
    proof Γ (P ⊃ Q) -> proof Γ (Q ⊃ R) -> proof Γ (P ⊃ R)
| ax_or_contr : forall {Γ} {P : prp Γ}, proof Γ (P ∨ P ⊃ P)
| ax_and_contr : forall {Γ} {P : prp Γ}, proof Γ (P ⊃ P ∧ P)
| ax_or_inl : forall {Γ} {P Q : prp Γ}, proof Γ (P ⊃ P ∨ Q)
| ax_and_eliml : forall {Γ} {P Q : prp Γ}, proof Γ (P ∧ Q ⊃ P)
| ax_or_comm : forall {Γ} {P Q : prp Γ}, proof Γ (P ∨ Q ⊃ Q ∨ P)
| ax_and_comm : forall {Γ} {P Q : prp Γ}, proof Γ (P ∧ Q ⊃ Q ∧ P)
| ax_or_distr : forall {Γ} {P Q R : prp Γ},
    proof Γ (P ⊃ Q) -> proof Γ (R ∨ P ⊃ R ∨ Q)
| ax_cur : forall {Γ} {P Q R : prp Γ},
    proof Γ (P ∧ Q ⊃ R) -> proof Γ (P ⊃ (Q ⊃ R))
| ax_uncur : forall {Γ} {P Q R : prp Γ},
    proof Γ (P ⊃ (Q ⊃ R)) -> proof Γ (P ∧ Q ⊃ R)
| ax_exfalso : forall {Γ} {P : prp Γ}, proof Γ (pFalse ⊃ P)
| ax_all_intro : forall {Γ} {P : prp Γ} {Q : prp (tN :: Γ)},
    proof (tN :: Γ) (pwk P ⊃ Q) -> proof Γ (P ⊃ pAll Q)
| ax_all_elim : forall {Γ} {Q : prp (tN :: Γ)} (t : tm Γ tN),
    proof Γ (pAll Q ⊃ psub1 Q t)
| ax_ex_intro : forall {Γ} {Q : prp (tN :: Γ)} (t : tm Γ tN),
    proof Γ (psub1 Q t ⊃ pEx Q)
| ax_ex_elim : forall {Γ} {P : prp Γ} {Q : prp (tN :: Γ)},
    proof (tN :: Γ) (Q ⊃ pwk P) -> proof Γ (pEx Q ⊃ P)
| ax_eq_refl : forall {Γ} (t : tm Γ tN), proof Γ (pEq t t)
| ax_leibniz : forall {Γ} {Q : prp (tN :: Γ)} (t s : tm Γ tN),
    proof Γ (pEq t s ⊃ (psub1 Q t ⊃ psub1 Q s))
| ax_succ_nonzero : forall {Γ} (t : tm Γ tN),
    proof Γ (pNot (pEq (tsuc t) tzero))
| ax_succ_inj : forall {Γ} (t s : tm Γ tN),
    proof Γ (pEq (tsuc t) (tsuc s) ⊃ pEq t s)
| ax_ind : forall {Γ} {Q : prp (tN :: Γ)},
    proof Γ ((psub1 Q tzero ∧ pAll (Q ⊃ psucc Q)) ⊃ pAll Q).

(** ** Derived rules *)

Definition d_id {Γ} (P : prp Γ) : proof Γ (P ⊃ P) :=
  ax_chain ax_and_contr ax_and_eliml.

Definition d_K {Γ} (P Q : prp Γ) : proof Γ (P ⊃ (Q ⊃ P)) :=
  ax_cur ax_and_eliml.

Definition d_or_inr {Γ} (P Q : prp Γ) : proof Γ (P ⊃ Q ∨ P) :=
  ax_chain ax_or_inl ax_or_comm.

Definition d_and_elimr {Γ} (P Q : prp Γ) : proof Γ (P ∧ Q ⊃ Q) :=
  ax_chain ax_and_comm ax_and_eliml.

(** Generalization: from [⊢_{Γ,x} Q] conclude [⊢_Γ ∀x. Q]. *)
Definition d_gen {Γ} {Q : prp (tN :: Γ)} (u : proof (tN :: Γ) Q) :
  proof Γ (pAll Q) :=
  ax_mp (ax_all_intro (ax_mp (d_K Q (pwk pTrue)) u)) ax_true.
