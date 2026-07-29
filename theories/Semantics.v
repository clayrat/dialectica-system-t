(** * Semantics: extensional equality and environment lemmas for the set model

    D2 steps 1-2: the lemma layer over Eval.v (which stays definitions-only,
    mirroring the upstream split Model.v vs Soundness.v).

    The central design decision (PROGRESS.md, D2 step 0): we stay *axiom-free*,
    like the NbE development, by working with an extensional partial
    equivalence [EEq] instead of Leibniz equality.  Leibniz equality between
    [tyden] values at arrow types would need functional extensionality (the
    [tlam] case of every commutation lemma produces a goal between Coq
    functions); [EEq] replaces it by "related arguments to related results",
    exactly as [SEq] does for the Kripke model in nbe-system-t/PER.v.  [EEq]
    is a PER, not an equivalence: at arrow types only functions that respect
    [EEq] are related to themselves.

    At base types, including booleans, [EEq] is Leibniz equality.  Reaching a
    boolean observation may nevertheless pass through higher-order values, so
    semantic statements must keep their environments and other inputs inside
    the PER domain.  Accordingly, [valid] (Dialectica.v) quantifies over
    self-related environments and counters.

    Contents:
    - [EEq]/[EEqE]: the PER on values, its pointwise lift to environments;
    - a congruence pack for constructing and consuming related values;
    - [opeden]/[subden]: the action of OPEs and parallel substitutions on
      environments — environments are nested tuples, so this layer is
      funext-free regardless;
    - evaluation-respect and renaming/substitution commutation lemmas, including
      the binder and head-instantiation environment cases;
    - facts about the equality program [teqb] (moved here from Eval.v and
      extended to [teqb_true_iff], needed for the Leibniz axiom in step 6). *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From NbE Require Import Syntax OPE Subst.
From SystemT Require Import Terms Eval.

Open Scope ty_scope.

(** ** The PER on semantic values *)

Fixpoint EEq (T : ty) : tyden T -> tyden T -> Prop :=
  match T return tyden T -> tyden T -> Prop with
  | tbase _ => fun a b => a = b
  | tarr T1 T2 => fun f g => forall a a', EEq T1 a a' -> EEq T2 (f a) (g a')
  | tprod T1 T2 => fun p q => EEq T1 (fst p) (fst q) /\ EEq T2 (snd p) (snd q)
  end.

Lemma EEq_sym : forall T (a b : tyden T), EEq T a b -> EEq T b a.
Proof.
  induction T as [b0 | T1 IH1 T2 IH2 | T1 IH1 T2 IH2]; simpl.
  - intros a b H; symmetry; exact H.
  - intros f g H a a' Ha. apply IH2. apply H. apply IH1. exact Ha.
  - intros p q [H1 H2]; split; [apply IH1; exact H1 | apply IH2; exact H2].
Qed.

Lemma EEq_trans : forall T (a b c : tyden T),
    EEq T a b -> EEq T b c -> EEq T a c.
Proof.
  induction T as [b0 | T1 IH1 T2 IH2 | T1 IH1 T2 IH2]; simpl.
  - intros a b c H1 H2; exact (eq_trans H1 H2).
  - intros f g h Hfg Hgh a a' Ha.
    apply IH2 with (b := g a').
    + apply Hfg; exact Ha.
    + apply Hgh. apply IH1 with (b := a); [apply EEq_sym; exact Ha | exact Ha].
  - intros p q r [H1 H2] [H3 H4];
      split; [exact (IH1 _ _ _ H1 H3) | exact (IH2 _ _ _ H2 H4)].
Qed.

(** The PER facts one actually reaches for: an element related to anything is
    related to itself. *)
Lemma EEq_refl_l : forall T (a b : tyden T), EEq T a b -> EEq T a a.
Proof.
  intros T a b H; exact (EEq_trans T _ _ _ H (EEq_sym T _ _ H)).
Qed.

Lemma EEq_refl_r : forall T (a b : tyden T), EEq T a b -> EEq T b b.
Proof.
  intros T a b H; exact (EEq_trans T _ _ _ (EEq_sym T _ _ H) H).
Qed.

(** ** The PER on environments (pointwise) *)

Fixpoint EEqE (Γ : cxt) : cxtden Γ -> cxtden Γ -> Prop :=
  match Γ return cxtden Γ -> cxtden Γ -> Prop with
  | [] => fun _ _ => True
  | T :: Γ' => fun ρ ρ' => EEq T (fst ρ) (fst ρ') /\ EEqE Γ' (snd ρ) (snd ρ')
  end.

Lemma EEqE_sym : forall Γ (ρ ρ' : cxtden Γ), EEqE Γ ρ ρ' -> EEqE Γ ρ' ρ.
Proof.
  induction Γ as [| T Γ IH]; simpl.
  - tauto.
  - intros ρ ρ' [H1 H2]; split; [apply EEq_sym; exact H1 | apply IH; exact H2].
Qed.

Lemma EEqE_trans : forall Γ (ρ1 ρ2 ρ3 : cxtden Γ),
    EEqE Γ ρ1 ρ2 -> EEqE Γ ρ2 ρ3 -> EEqE Γ ρ1 ρ3.
Proof.
  induction Γ as [| T Γ IH]; simpl.
  - tauto.
  - intros ρ1 ρ2 ρ3 [H1 H2] [H3 H4];
      split; [exact (EEq_trans T _ _ _ H1 H3) | exact (IH _ _ _ H2 H4)].
Qed.

Lemma EEqE_refl_l : forall Γ (ρ ρ' : cxtden Γ), EEqE Γ ρ ρ' -> EEqE Γ ρ ρ.
Proof.
  intros Γ ρ ρ' H; exact (EEqE_trans Γ _ _ _ H (EEqE_sym Γ _ _ H)).
Qed.

(** ** Congruence pack

    Small constructors/destructors for staying inside the PER domain — the
    validity scripts of D2 step 6 use these constantly ("self-related in,
    self-related out"). *)

Lemma EEq_app : forall {S T} (f f' : tyden (S ⇒ T)) (a a' : tyden S),
    EEq (S ⇒ T) f f' -> EEq S a a' -> EEq T (f a) (f' a').
Proof. intros S T f f' a a' Hf Ha; exact (Hf _ _ Ha). Qed.

Lemma EEq_pair : forall {S T} (a a' : tyden S) (b b' : tyden T),
    EEq S a a' -> EEq T b b' -> EEq (S × T) (a, b) (a', b').
Proof. intros; split; assumption. Qed.

Lemma EEq_fst : forall {S T} (p p' : tyden (S × T)),
    EEq (S × T) p p' -> EEq S (fst p) (fst p').
Proof. intros S T p p' H; exact (proj1 H). Qed.

Lemma EEq_snd : forall {S T} (p p' : tyden (S × T)),
    EEq (S × T) p p' -> EEq T (snd p) (snd p').
Proof. intros S T p p' H; exact (proj2 H). Qed.

Lemma EEqE_cons : forall {S Γ} (v v' : tyden S) (ρ ρ' : cxtden Γ),
    EEq S v v' -> EEqE Γ ρ ρ' -> EEqE (S :: Γ) (v, ρ) (v', ρ').
Proof. intros; split; assumption. Qed.

(** Variables respect the PER. *)
Lemma varden_EEqE : forall {Γ T} (x : var Γ T) (ρ ρ' : cxtden Γ),
    EEqE Γ ρ ρ' -> EEq T (varden x ρ) (varden x ρ').
Proof.
  induction x as [Γ S | Γ S T x IH]; simpl; intros ρ ρ' [H1 H2].
  - exact H1.
  - apply IH; exact H2.
Qed.

(** [EEqE] is exactly pointwise relatedness of variable lookups (converse of
    [varden_EEqE]) — handy for proving environment relations variable by
    variable. *)
Lemma EEqE_of_varden : forall {Γ} (ρ ρ' : cxtden Γ),
    (forall T (x : var Γ T), EEq T (varden x ρ) (varden x ρ')) ->
    EEqE Γ ρ ρ'.
Proof.
  induction Γ as [| T Γ IH]; simpl.
  - intros; exact I.
  - intros ρ ρ' H; split.
    + exact (H T vz).
    + apply IH; intros U y; exact (H U (vs y)).
Qed.

(** ** Environment actions of OPEs and substitutions

    Environments are nested tuples ([cxtden]), so these are plain functions
    and the variable-level commutation lemmas below are Leibniz equalities —
    no PER needed at this level. *)

Fixpoint opeden {Δ Γ} (o : ope Δ Γ) : cxtden Δ -> cxtden Γ :=
  match o in ope Δ0 Γ0 return cxtden Δ0 -> cxtden Γ0 with
  | ope_nil => fun ρ => ρ
  | ope_drop o' => fun ρ => opeden o' (snd ρ)
  | ope_keep o' => fun ρ => (fst ρ, opeden o' (snd ρ))
  end.

Fixpoint subden {Γ Δ} (σ : sub Δ Γ) (ρ : cxtden Δ) {struct Γ} : cxtden Γ :=
  match Γ as G return sub Δ G -> cxtden G with
  | [] => fun _ => tt
  | T :: Γ' => fun σ0 => (tmden (σ0 T vz) ρ, subden (fun U y => σ0 U (vs y)) ρ)
  end σ.

(** Variable-level commutation: the base cases of the [tm_ren]/[subst]
    commutation lemmas of D2 step 2. *)

Lemma varden_opeden : forall {Δ Γ} (o : ope Δ Γ) {T} (x : var Γ T) (ρ : cxtden Δ),
    varden (var_ren o x) ρ = varden x (opeden o ρ).
Proof.
  intros Δ Γ o; induction o as [| Δ0 Γ0 S o IH | Δ0 Γ0 S o IH].
  - intros T x ρ; reflexivity.
  - intros T x ρ; simpl; apply IH.
  - apply (var_cons_case S Γ0
             (fun T x => forall ρ,
                  varden (var_ren (ope_keep o) x) ρ
                  = varden x (opeden (ope_keep o) ρ))).
    + intros ρ; reflexivity.
    + intros U y ρ; simpl; apply IH.
Qed.

Lemma varden_subden : forall {Γ T} (x : var Γ T) {Δ} (σ : sub Δ Γ) (ρ : cxtden Δ),
    tmden (σ T x) ρ = varden x (subden σ ρ).
Proof.
  induction x as [Γ S | Γ S T x IH]; intros Δ σ ρ; simpl.
  - reflexivity.
  - apply (IH _ (fun U y => σ U (vs y))).
Qed.

(** ** The equality program

    [teqb] denotes [Nat.eqb], in any context and environment; the two
    corollaries are what the validity lemmas consume ([teqb_refl] for
    [ax_eq_refl], [teqb_true_iff] for [ax_leibniz]). *)

Lemma teqb_spec : forall {Γ} (ρ : cxtden Γ) (m n : nat),
    tmden teqb ρ m n = Nat.eqb m n.
Proof.
  intros Γ ρ m; induction m as [| m IH]; intros n; destruct n; simpl;
    try reflexivity.
  exact (IH n).
Qed.

Lemma teqb_true_iff : forall {Γ} (ρ : cxtden Γ) (m n : nat),
    tmden teqb ρ m n = true <-> m = n.
Proof.
  intros Γ ρ m n; rewrite teqb_spec; apply Nat.eqb_eq.
Qed.

Lemma teqb_refl : forall {Γ} (ρ : cxtden Γ) (n : nat),
    tmden teqb ρ n n = true.
Proof.
  intros Γ ρ n; apply teqb_true_iff; reflexivity.
Qed.

(** ** D2 step 2: evaluation commutes with renaming and substitution

    All statements are two-environment PER statements (`EEqE Δ ρ ρ' -> ...`)
    — the PER-domain premises are mandatory: the unrestricted versions are
    false axiom-free (an identity renaming would force arbitrary
    higher-order environment entries to be extensional). *)

Lemma opeden_id : forall {Γ} (ρ : cxtden Γ), opeden ope_id ρ = ρ.
Proof.
  induction Γ as [| T Γ IH]; simpl.
  - intros ρ; destruct ρ; reflexivity.
  - intros ρ; destruct ρ as [v ρ]; simpl; rewrite IH; reflexivity.
Qed.

Lemma opeden_EEqE : forall {Δ Γ} (o : ope Δ Γ) (ρ ρ' : cxtden Δ),
    EEqE Δ ρ ρ' -> EEqE Γ (opeden o ρ) (opeden o ρ').
Proof.
  intros Δ Γ o; induction o as [| Δ0 Γ0 S o IH | Δ0 Γ0 S o IH]; simpl.
  - intros ρ ρ' _; exact I.
  - intros ρ ρ' [H1 H2]; apply IH; exact H2.
  - intros ρ ρ' [H1 H2]; split; [exact H1 | apply IH; exact H2].
Qed.

(** Renaming: [tmden (tm_ren o t) ρ ≈ tmden t (opeden o ρ')]. *)
Lemma tmden_tm_ren : forall {Γ T} (t : tm Γ T) {Δ} (o : ope Δ Γ)
                            (ρ ρ' : cxtden Δ),
    EEqE Δ ρ ρ' ->
    EEq T (tmden (tm_ren o t) ρ) (tmden t (opeden o ρ')).
Proof.
  induction t as
    [ Γ
    | Γ t IHt
    | Γ T z IHz s IHs n IHn
    | Γ | Γ | Γ
    | Γ T b IHb t1 IH1 t2 IH2
    | Γ T x
    | Γ S T b IHb
    | Γ S T f IHf u IHu
    | Γ S T a IHa b IHb
    | Γ S T p IHp
    | Γ S T p IHp ];
    intros Δ o ρ ρ' Hρ; simpl.
  - reflexivity.
  - f_equal; apply IHt; exact Hρ.
  - specialize (IHn _ o ρ ρ' Hρ); simpl in IHn; rewrite IHn; clear IHn.
    induction (tmden n (opeden o ρ')) as [| k IHk]; simpl.
    + apply IHz; exact Hρ.
    + exact (IHs _ o ρ ρ' Hρ k k eq_refl _ _ IHk).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - specialize (IHb _ o ρ ρ' Hρ); simpl in IHb; rewrite IHb.
    destruct (tmden b (opeden o ρ')); [apply IH1 | apply IH2]; exact Hρ.
  - rewrite varden_opeden.
    apply varden_EEqE; apply opeden_EEqE; exact Hρ.
  - intros a a' Ha.
    apply (IHb _ (ope_keep o) (a, ρ) (a', ρ')).
    exact (conj Ha Hρ).
  - exact (IHf _ o ρ ρ' Hρ _ _ (IHu _ o ρ ρ' Hρ)).
  - split; [apply IHa | apply IHb]; exact Hρ.
  - destruct (IHp _ o ρ ρ' Hρ) as [H1 _]; exact H1.
  - destruct (IHp _ o ρ ρ' Hρ) as [_ H2]; exact H2.
Qed.

(** The fundamental respect lemma is the identity-OPE instance. *)
Lemma tmden_EEqE : forall {Γ T} (t : tm Γ T) (ρ ρ' : cxtden Γ),
    EEqE Γ ρ ρ' -> EEq T (tmden t ρ) (tmden t ρ').
Proof.
  intros Γ T t ρ ρ' Hρ.
  pose proof (tmden_tm_ren t ope_id ρ ρ' Hρ) as H.
  rewrite tm_ren_id, opeden_id in H; exact H.
Qed.

(** Environments built by [subden] from entrywise-related substitutions are
    related — the two substitutions may have different source contexts (the
    [sub_lift] case below relates [S :: Δ] with [Δ]). *)
Lemma subden_entrywise : forall {Γ Δ1 Δ2} (σ1 : sub Δ1 Γ) (σ2 : sub Δ2 Γ)
                                (ρ1 : cxtden Δ1) (ρ2 : cxtden Δ2),
    (forall T (x : var Γ T), EEq T (tmden (σ1 T x) ρ1) (tmden (σ2 T x) ρ2)) ->
    EEqE Γ (subden σ1 ρ1) (subden σ2 ρ2).
Proof.
  intros Γ; induction Γ as [| T Γ IH]; simpl.
  - intros; exact I.
  - intros Δ1 Δ2 σ1 σ2 ρ1 ρ2 H; split.
    + exact (H T vz).
    + apply IH; intros U y; exact (H U (vs y)).
Qed.

Corollary subden_EEqE : forall {Γ Δ} (σ : sub Δ Γ) (ρ ρ' : cxtden Δ),
    EEqE Δ ρ ρ' -> EEqE Γ (subden σ ρ) (subden σ ρ').
Proof.
  intros Γ Δ σ ρ ρ' Hρ; apply subden_entrywise;
    intros U y; apply tmden_EEqE; exact Hρ.
Qed.

(** The binder case: pushing a lifted substitution under an extended
    environment. *)
Lemma subden_sub_lift : forall {Γ Δ S} (σ : sub Δ Γ) (a a' : tyden S)
                               (ρ ρ' : cxtden Δ),
    EEq S a a' -> EEqE Δ ρ ρ' ->
    EEqE (S :: Γ) (subden (sub_lift σ) (a, ρ)) (a', subden σ ρ').
Proof.
  intros Γ Δ S σ a a' ρ ρ' Ha Hρ; split.
  - exact Ha.
  - apply subden_entrywise; intros U y.
    pose proof (@tmden_tm_ren Δ U (σ U y) (S :: Δ) wk (a, ρ) (a', ρ')
                  (conj Ha Hρ)) as H.
    simpl in H; rewrite opeden_id in H; exact H.
Qed.

(** The [sub_at0] instance used by [diaT]'s quantifier cases and the
    quantifier axioms: instantiating the head variable at a numeric term
    while renaming the rest. *)
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

(** Substitution: [tmden (subst σ t) ρ ≈ tmden t (subden σ ρ')]. *)
Lemma tmden_subst : forall {Γ T} (t : tm Γ T) {Δ} (σ : sub Δ Γ)
                           (ρ ρ' : cxtden Δ),
    EEqE Δ ρ ρ' ->
    EEq T (tmden (subst σ t) ρ) (tmden t (subden σ ρ')).
Proof.
  induction t as
    [ Γ
    | Γ t IHt
    | Γ T z IHz s IHs n IHn
    | Γ | Γ | Γ
    | Γ T b IHb t1 IH1 t2 IH2
    | Γ T x
    | Γ S T b IHb
    | Γ S T f IHf u IHu
    | Γ S T a IHa b IHb
    | Γ S T p IHp
    | Γ S T p IHp ];
    intros Δ σ ρ ρ' Hρ; simpl.
  - reflexivity.
  - f_equal; apply IHt; exact Hρ.
  - specialize (IHn _ σ ρ ρ' Hρ); simpl in IHn; rewrite IHn; clear IHn.
    induction (tmden n (subden σ ρ')) as [| k IHk]; simpl.
    + apply IHz; exact Hρ.
    + exact (IHs _ σ ρ ρ' Hρ k k eq_refl _ _ IHk).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - specialize (IHb _ σ ρ ρ' Hρ); simpl in IHb; rewrite IHb.
    destruct (tmden b (subden σ ρ')); [apply IH1 | apply IH2]; exact Hρ.
  - rewrite <- (varden_subden x σ ρ').
    apply tmden_EEqE; exact Hρ.
  - intros a a' Ha.
    apply EEq_trans with (b := tmden b (subden (sub_lift σ) (a, ρ))).
    + apply (IHb _ (sub_lift σ) (a, ρ) (a, ρ)).
      exact (conj (EEq_refl_l _ _ _ Ha) (EEqE_refl_l _ _ _ Hρ)).
    + apply tmden_EEqE.
      apply subden_sub_lift; [exact Ha | exact Hρ].
  - exact (IHf _ σ ρ ρ' Hρ _ _ (IHu _ σ ρ ρ' Hρ)).
  - split; [apply IHa | apply IHb]; exact Hρ.
  - destruct (IHp _ σ ρ ρ' Hρ) as [H1 _]; exact H1.
  - destruct (IHp _ σ ρ ρ' Hρ) as [_ H2]; exact H2.
Qed.
