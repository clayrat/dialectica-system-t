(** * Eval: the set-theoretic semantics of System T

    A standard evaluator into Coq types (Coq is the meta-language, so this is
    ~15 lines with intrinsic syntax).  Interpretation-independent: it is the
    "intended model" complementing the Kripke model of the NbE development,
    and it gives the Dialectica matrix its meaning (Dialectica.v) — but it
    would serve any other interpretation, or a direct Tarski semantics of HA,
    just as well.

    Totality of evaluation is inherited from the meta-language: [trec] maps to
    [nat_rect], so running extracted programs needs no normalization theorem
    for T itself. *)

From Stdlib Require Import List.
Import ListNotations.
From NbE Require Import Syntax.
From SystemT Require Import Terms.

Open Scope ty_scope.

Definition bden (b : base) : Type :=
  match b with
  | bNat => nat
  | bUnit => unit
  | bBool => bool
  end.

Fixpoint tyden (T : ty) : Type :=
  match T with
  | tbase b => bden b
  | tarr T1 T2 => tyden T1 -> tyden T2
  | tprod T1 T2 => (tyden T1 * tyden T2)%type
  end.

Fixpoint cxtden (Γ : cxt) : Type :=
  match Γ with
  | [] => unit
  | T :: Γ' => (tyden T * cxtden Γ')%type
  end.

Fixpoint varden {Γ T} (x : var Γ T) : cxtden Γ -> tyden T :=
  match x in var Γ0 T0 return cxtden Γ0 -> tyden T0 with
  | vz => fun ρ => fst ρ
  | vs y => fun ρ => varden y (snd ρ)
  end.

Fixpoint tmden {Γ T} (t : tm Γ T) : cxtden Γ -> tyden T :=
  match t in tm Γ0 T0 return cxtden Γ0 -> tyden T0 with
  | tzero => fun _ => 0
  | tsuc t => fun ρ => S (tmden t ρ)
  | @trec _ T1 z s n =>
      fun ρ => nat_rect (fun _ => tyden T1)
                        (tmden z ρ) (fun k r => tmden s ρ k r) (tmden n ρ)
  | tunit => fun _ => tt
  | ttrue => fun _ => true
  | tfalse => fun _ => false
  | tif b t1 t2 => fun ρ => if tmden b ρ then tmden t1 ρ else tmden t2 ρ
  | tvar x => varden x
  | tlam b => fun ρ v => tmden b (v, ρ)
  | tapp t u => fun ρ => tmden t ρ (tmden u ρ)
  | tpair a b => fun ρ => (tmden a ρ, tmden b ρ)
  | tfst p => fun ρ => fst (tmden p ρ)
  | tsnd p => fun ρ => snd (tmden p ρ)
  end.

(** The equality program [teqb] means what it should on the diagonal. *)
Lemma teqb_refl : forall n, tmden (@teqb []) tt n n = true.
Proof. induction n as [|n IH]; [reflexivity | exact IH]. Qed.
