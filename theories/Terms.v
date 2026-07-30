(** * Terms: a System T utility kit on top of the NbE development

    Generic infrastructure over the shared syntax (nbe-system-t, namespace
    [NbE]): project-specific substitution instances built from the upstream
    combinators, application/variable notations, boolean connectives, and
    addition as programs.

    Nothing in this file mentions formulas or any interpretation — it is the
    common substrate for HA.v (the logic) and Dialectica.v (the
    interpretation), and would equally serve other interpretations
    (modified realizability, Diller–Nahm, ...).

    We build on: OPEs with [tm_ren] for renaming/weakening, and parallel
    substitution [sub Δ Γ] / [subst] — together with its already-proved fusion
    lemma library consumed by the soundness proof (D2).  Note the
    NbE convention [sub Δ Γ = forall T, var Γ T -> tm Δ T] (target first). *)

From Stdlib Require Import List.
Import ListNotations.
From NbE Require Import Syntax OPE Subst.

Open Scope ty_scope.

(** ** Substitution combinators *)

(** Weakening a term by one type.  OPEs that discard longer prefixes use
    upstream [drop_prefix]. *)
Definition wk1 {Γ S T} (t : tm Γ T) : tm (S :: Γ) T := tm_ren wk t.

(** Substituting a numeric term [n] for the head variable while renaming the
    remaining variables by an OPE [o]: used to instantiate a term living in
    [tN :: Γ] deep inside some larger context [Δ].  Upstream [ext_sub]
    extends the renaming-as-substitution [sren o] with the new head. *)
Definition sub_at0 {Δ Γ} (o : ope Δ Γ) (n : tm Δ tN) : sub Δ (tN :: Γ) :=
  ext_sub (sren o) n.

(** The successor substitution [x ↦ S x] on the head [tN] variable (used by
    HA to state induction): extend weakening-as-substitution with [S x]. *)
Definition sub_succ {Γ} : sub (tN :: Γ) (tN :: Γ) :=
  ext_sub (sren wk) (tsuc (tvar vz)).

(** Transporting a term along an equality of types (the equalities come from
    the W/C-invariance lemmas in Dialectica.v; kept generic here). *)
Definition tcast {Γ T U} (e : T = U) (t : tm Γ T) : tm Γ U :=
  match e in _ = U0 return tm Γ U0 with
  | eq_refl => t
  end.

(** ** Notations *)

Declare Scope tm_scope.
Notation "t · u" := (tapp t u) (at level 40, left associativity) : tm_scope.
Open Scope tm_scope.

Notation v0 := (tvar vz).
Notation v1 := (tvar (vs vz)).
Notation v2 := (tvar (vs (vs vz))).
Notation v3 := (tvar (vs (vs (vs vz)))).
Notation v4 := (tvar (vs (vs (vs (vs vz))))).

(** ** Boolean connectives as programs *)

Definition tandb {Γ} (a b : tm Γ tBool) : tm Γ tBool := tif a b tfalse.
Definition timplb {Γ} (a b : tm Γ tBool) : tm Γ tBool := tif a b ttrue.
Definition tnegb {Γ} (a : tm Γ tBool) : tm Γ tBool := tif a tfalse ttrue.

(** ** Addition as a System T program, recursing on the *first* argument:
    [plus = λm n. rec n (λm' r. S r) m].  (So [0 + n] computes but [m + 0]
    does not — [∀x. x + 0 = x] genuinely needs induction.) *)
Definition tplus {Γ} : tm Γ (tN ⇒ tN ⇒ tN) :=
  tlam (tlam (trec v0 (tlam (tlam (tsuc v0))) v1)).
