(** * Semantics: Dialectica-specific extensions of the set model

    The reusable set-theoretic evaluator and its axiom-free PER metatheory
    live upstream in [NbE.SetModel] and [NbE.SetModelPER].  This file contains
    only facts tied to the local System T utility terms and substitutions:

    - environment equations for [sub_at0] and [sub_succ];
    - denotation of the local transport [tcast];
    - the Boolean implication elimination used by Dialectica validity.

    Generic results such as [EEq]/[EEqE], evaluator commutation,
    [tyden_cast], [tmden_defeq], and [triv_EEq] are imported from
    [NbE.SetModelPER]. *)

From Stdlib Require Import List Bool.
Import ListNotations.
From NbE Require Import Syntax OPE Subst SetModel SetModelPER.
From SystemT Require Import Terms.

Open Scope ty_scope.

(** ** Project-specific environment equations *)

(** Instantiating the head numeric variable while renaming the tail. *)
Lemma subden_sub_at0 : forall {Δ Γ} (o : ope Δ Γ) (n : tm Δ tN)
                              (ρ ρ' : cxtden Δ),
    EEqE Δ ρ ρ' ->
    EEqE (tN :: Γ) (subden (sub_at0 o n) ρ) (tmden n ρ', opeden o ρ').
Proof.
  intros Δ Γ o n ρ ρ' Hρ.
  apply EEqE_of_varden.
  apply (var_cons_case tN Γ
           (fun T x => EEq T (varden x (subden (sub_at0 o n) ρ))
                             (varden x (tmden n ρ', opeden o ρ')))).
  - exact (tmden_EEqE n ρ ρ' Hρ).
  - intros U y.
    rewrite <- (varden_subden (vs y) (sub_at0 o n) ρ).
    simpl; rewrite varden_opeden.
    apply varden_EEqE; apply opeden_EEqE; exact Hρ.
Qed.

(** [sub_succ] denotes taking the successor of the head entry. *)
Lemma subden_sub_succ : forall {Δ} (ρ ρ' : cxtden (tN :: Δ)),
    EEqE (tN :: Δ) ρ ρ' ->
    EEqE (tN :: Δ) (subden sub_succ ρ) (S (fst ρ'), snd ρ').
Proof.
  intros Δ ρ ρ' Hρ.
  apply EEqE_of_varden.
  apply (var_cons_case tN Δ
           (fun T x => EEq T (varden x (subden sub_succ ρ))
                             (varden x (S (fst ρ'), snd ρ')))).
  - simpl; f_equal; exact (proj1 Hρ).
  - intros U y.
    rewrite <- (varden_subden (vs y) sub_succ ρ).
    change (EEq U (varden (var_ren wk y) ρ) (varden y (snd ρ'))).
    rewrite varden_opeden, opeden_wk.
    apply varden_EEqE; exact (proj2 Hρ).
Qed.

(** ** Local term utilities *)

Lemma tmden_tcast : forall {Γ T U} (e : T = U) (t : tm Γ T) (ρ : cxtden Γ),
    tmden (tcast e t) ρ = tyden_cast e (tmden t ρ).
Proof. intros Γ T U e; destruct e; intros; reflexivity. Qed.

Lemma implb_true_elim : forall a b : bool,
    implb a b = true -> a = true -> b = true.
Proof. intros a b H Ha; rewrite Ha in H; exact H. Qed.
