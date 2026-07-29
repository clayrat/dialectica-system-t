(** * Terms: a System T utility kit on top of the NbE development

    Generic infrastructure over the shared syntax (nbe-system-t, namespace
    [NbE]): a few substitution combinators the NbE side does not provide,
    application/variable notations, boolean connectives as programs, canonical
    inhabitants, and decidable equality of naturals as a T-program.

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

(** Case analysis on a variable in a non-empty context, packaged once so that
    the dependent match trickery is not repeated. *)
Definition vcase {Γ S T} (x : var (S :: Γ) T) :
  forall A : ty -> Type, A S -> (forall T', var Γ T' -> A T') -> A T :=
  match x in var Γ0 T0
        return match Γ0 with
               | [] => IDProp
               | S0 :: Γ0' =>
                   forall A : ty -> Type,
                     A S0 -> (forall T', var Γ0' T' -> A T') -> A T0
               end
  with
  | vz => fun A z s => z
  | vs y => fun A z s => s _ y
  end.

(** Weakening by one type, and two composite weakenings (Dialectica's
    realizers need two binders for [diaT]'s λλ, five for the induction
    search). *)
Definition wk1 {Γ S T} (t : tm Γ T) : tm (S :: Γ) T := tm_ren wk t.

Definition wkn2 {Γ S1 S2} : ope (S1 :: S2 :: Γ) Γ :=
  ope_drop (ope_drop ope_id).

Definition wkn5 {Γ S1 S2 S3 S4 S5} : ope (S1 :: S2 :: S3 :: S4 :: S5 :: Γ) Γ :=
  ope_drop (ope_drop (ope_drop wkn2)).

(** Substituting for the head variable only (the substitution object behind
    [subst1]; first-class so it can be pushed through formulas). *)
Definition sub1 {Γ S} (s : tm Γ S) : sub Γ (S :: Γ) :=
  fun T x => vcase x (tm Γ) s (fun T' y => tvar y).

(** Substituting a numeric term [n] for the head variable while renaming the
    remaining variables by an OPE [o]: used to instantiate a term living in
    [tN :: Γ] deep inside some larger context [Δ]. *)
Definition sub_at0 {Δ Γ} (o : ope Δ Γ) (n : tm Δ tN) : sub Δ (tN :: Γ) :=
  fun T x => vcase x (tm Δ) n (fun T' y => tvar (var_ren o y)).

(** The successor substitution [x ↦ S x] on the head [tN] variable (used by
    HA to state induction). *)
Definition sub_succ {Γ} : sub (tN :: Γ) (tN :: Γ) :=
  fun T x =>
    vcase x (tm (tN :: Γ)) (tsuc (tvar vz)) (fun T' y => tvar (vs y)).

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

(** ** Canonical inhabitants

    Every System T type is inhabited — used for the "dummy" moves that some
    Dialectica realizers must produce (cf. [W_member]/[C_member] in Bauer's
    version). *)
Fixpoint tdefault {Γ} (T : ty) : tm Γ T :=
  match T with
  | tbase bNat => tzero
  | tbase bUnit => tunit
  | tbase bBool => ttrue
  | tarr T1 T2 => tlam (tdefault T2)
  | tprod T1 T2 => tpair (tdefault T1) (tdefault T2)
  end.

(** ** Decidable equality of naturals, as a System T program:
    [eqb = λm. rec iszero (λm' r. λn. rec false (λn' _. r n') n) m]. *)
Definition tiszero {Γ} : tm Γ (tN ⇒ tBool) :=
  tlam (trec ttrue (tlam (tlam tfalse)) v0).

Definition teqb {Γ} : tm Γ (tN ⇒ tN ⇒ tBool) :=
  tlam (trec tiszero
             (tlam (tlam (tlam (trec tfalse
                                     (tlam (tlam (v3 · v1)))
                                     v0))))
             v0).
