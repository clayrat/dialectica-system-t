(** * Semantics: evaluator infrastructure for the set/PER model

    Infrastructure used by D2 steps 1-3, 5, and 6 and D2.5 step 4, layered
    over Eval.v (which stays definitions-only, mirroring the upstream split
    Model.v vs Soundness.v).

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
    - transport of denotations along type equalities, value-level weakening,
      and the concrete environment equations used by formula semantics;
    - canonical semantic defaults and their correspondence with [tdefault],
      used by the induction search;
    - facts about the equality program [teqb] (moved here from Eval.v and
      extended to [teqb_true_iff], needed for the Leibniz axiom in step 6);
    - [tmden_defeq]: βη-convertible terms have PER-related denotations, the
      bridge used to transfer validity across NbE normalization in D2.5;
    - [triv]: the PER-trivial types, whose inhabitants are all
      interchangeable — the semantic side conditions of the D3
      characteristic principles. *)

From Stdlib Require Import List PeanoNat Eqdep_dec.
Import ListNotations.
From NbE Require Import Syntax OPE Subst DefEq.
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

Lemma EEqE_refl_r : forall Γ (ρ ρ' : cxtden Γ), EEqE Γ ρ ρ' -> EEqE Γ ρ' ρ'.
Proof.
  intros Γ ρ ρ' H; exact (EEqE_trans Γ _ _ _ (EEqE_sym Γ _ _ H) H).
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

(** ** D2 step 3 toolkit: transport along type equalities

    The formula-substitution lemmas relate values at [W (psub σ A)] with
    values at [W A] — equal types, but not syntactically so.  [tyden_cast]
    transports; the collapse lemmas below let us forget *how* an equality
    proof was built ([ty] has decidable equality, so UIP on [ty] is a
    theorem, via upstream [ty_eq_dec]). *)

Definition tyden_cast {T U : ty} (e : T = U) : tyden T -> tyden U :=
  fun v => eq_rect T tyden v U e.

Lemma ty_uip : forall {T U : ty} (e e' : T = U), e = e'.
Proof. intros; apply (UIP_dec ty_eq_dec). Qed.

Lemma tyden_cast_refl : forall {T} (e : T = T) (v : tyden T),
    tyden_cast e v = v.
Proof. intros T e v; rewrite (ty_uip e eq_refl); reflexivity. Qed.

Lemma tmden_tcast : forall {Γ T U} (e : T = U) (t : tm Γ T) (ρ : cxtden Γ),
    tmden (tcast e t) ρ = tyden_cast e (tmden t ρ).
Proof. intros Γ T U e; destruct e; intros; reflexivity. Qed.

Lemma tyden_cast_sym_cancel : forall {T U} (e : T = U) (v : tyden T),
    tyden_cast (eq_sym e) (tyden_cast e v) = v.
Proof. intros T U e; destruct e; reflexivity. Qed.

(** How casts act on products and arrows, given proofs of the component
    equalities — by UIP, the ambient proof [e] is irrelevant. *)

Lemma tyden_cast_prod : forall {S S' T T'} (eS : S = S') (eT : T = T')
                               (e : (S × T) = (S' × T')) (p : tyden (S × T)),
    tyden_cast e p = (tyden_cast eS (fst p), tyden_cast eT (snd p)).
Proof.
  intros S S' T T' eS eT e p; destruct eS, eT.
  rewrite (ty_uip e eq_refl); destruct p; reflexivity.
Qed.

Corollary tyden_cast_prod_fst : forall {S S' T T'} (eS : S = S') (eT : T = T')
                                       (e : (S × T) = (S' × T'))
                                       (p : tyden (S × T)),
    fst (tyden_cast e p) = tyden_cast eS (fst p).
Proof. intros; rewrite (tyden_cast_prod eS eT); reflexivity. Qed.

Corollary tyden_cast_prod_snd : forall {S S' T T'} (eS : S = S') (eT : T = T')
                                       (e : (S × T) = (S' × T'))
                                       (p : tyden (S × T)),
    snd (tyden_cast e p) = tyden_cast eT (snd p).
Proof. intros; rewrite (tyden_cast_prod eS eT); reflexivity. Qed.

Lemma tyden_cast_arr : forall {S S' T T'} (eS : S = S') (eT : T = T')
                              (e : (S ⇒ T) = (S' ⇒ T'))
                              (f : tyden (S ⇒ T)) (a : tyden S'),
    tyden_cast e f a = tyden_cast eT (f (tyden_cast (eq_sym eS) a)).
Proof.
  intros S S' T T' eS eT e f a; destruct eS, eT.
  rewrite (ty_uip e eq_refl); reflexivity.
Qed.

Lemma EEq_cast : forall {T U} (e : T = U) (v v' : tyden T),
    EEq T v v' -> EEq U (tyden_cast e v) (tyden_cast e v').
Proof. intros T U e; destruct e; intros; assumption. Qed.

(** ** Weakening at the value level, and instance environment lemmas

    [tmden_wk1_EEq]/[tmden_wk2_EEq] evaluate a weakened term by dropping the
    extra environment entries; the [opeden_*]/[subden_*] instances compute
    the environment actions of the concrete OPEs/substitutions used by
    [diaT] and the HA axioms. *)

Lemma tmden_wk1_EEq : forall {Γ S T} (t : tm Γ T) (v v' : tyden S)
                             (ρ ρ' : cxtden Γ),
    EEq S v v' -> EEqE Γ ρ ρ' ->
    EEq T (tmden (wk1 t) (v, ρ)) (tmden t ρ').
Proof.
  intros Γ S T t v v' ρ ρ' Hv Hρ.
  pose proof (@tmden_tm_ren Γ T t (S :: Γ) wk (v, ρ) (v', ρ')
                (conj Hv Hρ)) as H.
  simpl in H; rewrite opeden_id in H; exact H.
Qed.

Lemma tmden_wk2_EEq : forall {Γ S1 S2 T} (t : tm Γ T)
                             (v1 v1' : tyden S1) (v2 v2' : tyden S2)
                             (ρ ρ' : cxtden Γ),
    EEq S1 v1 v1' -> EEq S2 v2 v2' -> EEqE Γ ρ ρ' ->
    EEq T (tmden (wk1 (wk1 t)) (v1, (v2, ρ))) (tmden t ρ').
Proof.
  intros Γ S1 S2 T t v1 v1' v2 v2' ρ ρ' H1 H2 Hρ.
  apply EEq_trans with (b := tmden (wk1 t) (v2', ρ')).
  - exact (tmden_wk1_EEq (wk1 t) v1 v1' (v2, ρ) (v2', ρ') H1 (conj H2 Hρ)).
  - exact (tmden_wk1_EEq t v2' v2' ρ' ρ'
             (EEq_refl_r _ _ _ H2) (EEqE_refl_r _ _ _ Hρ)).
Qed.

Lemma opeden_wk : forall {Γ S} (ρ : cxtden (S :: Γ)),
    opeden wk ρ = snd ρ.
Proof. intros Γ S ρ; simpl; apply opeden_id. Qed.

Lemma opeden_wkn2 : forall {Γ S1 S2} (ρ : cxtden (S1 :: S2 :: Γ)),
    opeden wkn2 ρ = snd (snd ρ).
Proof. intros; simpl; apply opeden_id. Qed.

Lemma opeden_wkn5 : forall {Γ S1 S2 S3 S4 S5}
                           (ρ : cxtden (S1 :: S2 :: S3 :: S4 :: S5 :: Γ)),
    opeden wkn5 ρ = snd (snd (snd (snd (snd ρ)))).
Proof. intros; simpl; apply opeden_id. Qed.

(** [sub1 t] denotes environment extension by [tmden t]. *)
Lemma subden_sub1 : forall {Δ S} (t : tm Δ S) (ρ ρ' : cxtden Δ),
    EEqE Δ ρ ρ' ->
    EEqE (S :: Δ) (subden (sub1 t) ρ) (tmden t ρ', ρ').
Proof.
  intros Δ S t ρ ρ' Hρ.
  apply EEqE_of_varden.
  apply (var_cons_case S Δ
           (fun T x => EEq T (varden x (subden (sub1 t) ρ))
                             (varden x (tmden t ρ', ρ')))).
  - exact (tmden_EEqE t ρ ρ' Hρ).
  - intros U y.
    rewrite <- (varden_subden (vs y) (sub1 t) ρ).
    simpl; apply varden_EEqE; exact Hρ.
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
    simpl; apply varden_EEqE; exact (proj2 Hρ).
Qed.

(** ** D2 step 5 prerequisites: canonical defaults, and the other cast cancel *)

(** The semantic counterpart of [tdefault]. *)
Fixpoint tydefault (T : ty) : tyden T :=
  match T with
  | tbase bNat => 0
  | tbase bUnit => tt
  | tbase bBool => true
  | tarr T1 T2 => fun _ => tydefault T2
  | tprod T1 T2 => (tydefault T1, tydefault T2)
  end.

Lemma tydefault_EEq : forall T, EEq T (tydefault T) (tydefault T).
Proof.
  induction T as [b | T1 IH1 T2 IH2 | T1 IH1 T2 IH2]; simpl.
  - destruct b; reflexivity.
  - intros a a' _; exact IH2.
  - split; [exact IH1 | exact IH2].
Qed.

(** [tdefault] denotes [tydefault] in any environment (no PER premise: the
    environment is never consulted). *)
Lemma tmden_tdefault : forall (T : ty) {Γ} (ρ : cxtden Γ),
    EEq T (tmden (tdefault T) ρ) (tydefault T).
Proof.
  induction T as [b | T1 IH1 T2 IH2 | T1 IH1 T2 IH2]; intros Γ ρ; simpl.
  - destruct b; reflexivity.
  - intros a a' _; exact (IH2 (T1 :: Γ) (a, ρ)).
  - split; [exact (IH1 Γ ρ) | exact (IH2 Γ ρ)].
Qed.

Lemma tyden_cast_cancel_sym : forall {T U} (e : T = U) (v : tyden U),
    tyden_cast e (tyden_cast (eq_sym e) v) = v.
Proof. intros T U e; destruct e; reflexivity. Qed.

(** ** D2 step 6 helpers *)

Lemma tyden_cast_trans : forall {T U V} (e1 : T = U) (e2 : U = V) (v : tyden T),
    tyden_cast e2 (tyden_cast e1 v) = tyden_cast (eq_trans e1 e2) v.
Proof. intros T U V e1 e2 v; destruct e1, e2; reflexivity. Qed.

Lemma implb_true_elim : forall a b : bool, implb a b = true -> a = true -> b = true.
Proof. intros a b H Ha; rewrite Ha in H; exact H. Qed.

(** ** D2.5 step 4: evaluation respects definitional equality

    The bridge between the NbE metatheory and the set model: βη-convertible
    terms have PER-related denotations.  Stated observationally, as always —
    the η-rules make the Leibniz version funext-dependent. *)

Lemma natrec_EEq : forall (T : ty) (z z' : tyden T)
                          (s s' : tyden (tN ⇒ T ⇒ T)) (n n' : nat),
    EEq T z z' -> EEq (tN ⇒ T ⇒ T) s s' -> n = n' ->
    EEq T (nat_rect (fun _ => tyden T) z (fun k r => s k r) n)
          (nat_rect (fun _ => tyden T) z' (fun k r => s' k r) n').
Proof.
  intros T z z' s s' n n' Hz Hs Hn; subst n'.
  induction n as [| k IH]; simpl.
  - exact Hz.
  - exact (Hs k k eq_refl _ _ IH).
Qed.

Lemma if_EEq : forall (T : ty) (b b' : bool) (x x' y y' : tyden T),
    b = b' -> EEq T x x' -> EEq T y y' ->
    EEq T (if b then x else y) (if b' then x' else y').
Proof.
  intros T b b' x x' y y' Hb Hx Hy; subst b'.
  destruct b; assumption.
Qed.

(** β-substitution semantically: substituting the head variable is
    environment extension by the substituted term's value. *)
Lemma tmden_subst1 : forall {Γ S T} (t : tm (S :: Γ) T) (s : tm Γ S)
                            (ρ ρ' : cxtden Γ),
    EEqE Γ ρ ρ' ->
    EEq T (tmden (subst1 t s) ρ) (tmden t (tmden s ρ', ρ')).
Proof.
  intros Γ S T t s ρ ρ' Hρ.
  eapply EEq_trans.
  - exact (tmden_subst t _ ρ ρ' Hρ).
  - apply tmden_EEqE.
    eapply EEqE_trans.
    + apply (subden_entrywise _ (sub1 s)).
      apply (var_cons_case S Γ
               (fun U x =>
                  EEq U (tmden ((fun U0 (x0 : var (S :: Γ) U0) =>
                            (match x0 in var G U'
                                   return tm (tl G) (hd S G) -> tm (tl G) U'
                             with
                             | vz => fun s0 => s0
                             | vs y => fun _ => tvar y
                             end) s) U x) ρ')
                        (tmden (sub1 s U x) ρ'))).
      * exact (tmden_EEqE s ρ' ρ' (EEqE_refl_r _ _ _ Hρ)).
      * intros U y.
        exact (varden_EEqE y ρ' ρ' (EEqE_refl_r _ _ _ Hρ)).
    + exact (subden_sub1 s ρ' ρ' (EEqE_refl_r _ _ _ Hρ)).
Qed.

(** The bridge, by induction on the derivation. *)
Lemma tmden_defeq : forall {Γ T} (t t' : tm Γ T),
    defeq Γ T t t' ->
    forall (ρ ρ' : cxtden Γ), EEqE Γ ρ ρ' ->
    EEq T (tmden t ρ) (tmden t' ρ').
Proof.
  intros Γ T t t' Hd; induction Hd as
    [ Γ S T t s
    | Γ T z s
    | Γ T z s n
    | Γ T t f
    | Γ T t f
    | Γ S T a b
    | Γ S T a b
    | Γ S T t
    | Γ S T t
    | Γ S T t t' Hd IH
    | Γ S T r r' s s' Hd1 IH1 Hd2 IH2
    | Γ n n' Hd IH
    | Γ T z z' s s' n n' Hdz IHz Hds IHs Hdn IHn
    | Γ T c c' t t' f f' Hdc IHc Hdt IHt Hdf IHf
    | Γ S T a a' b b' Hda IHa Hdb IHb
    | Γ S T t t' Hd IH
    | Γ S T t t' Hd IH
    | Γ T t
    | Γ T t t' Hd IH
    | Γ T t1 t2 t3 Hd1 IH1 Hd2 IH2 ];
    intros ρ ρ' Hρ.
  - (* β *)
    exact (EEq_sym _ _ _ (tmden_subst1 t s ρ' ρ (EEqE_sym _ _ _ Hρ))).
  - (* rec zero *)
    exact (tmden_EEqE z ρ ρ' Hρ).
  - (* rec suc: both sides converge by ι *)
    exact (tmden_EEqE (tapp (tapp s n) (trec z s n)) ρ ρ' Hρ).
  - (* if true *)
    exact (tmden_EEqE t ρ ρ' Hρ).
  - (* if false *)
    exact (tmden_EEqE f ρ ρ' Hρ).
  - (* fst pair *)
    exact (tmden_EEqE a ρ ρ' Hρ).
  - (* snd pair *)
    exact (tmden_EEqE b ρ ρ' Hρ).
  - (* η *)
    intros a a' Ha.
    exact (tmden_wk1_EEq t a a' ρ ρ' Ha Hρ _ _ Ha).
  - (* pair η *)
    exact (conj (proj1 (tmden_EEqE t ρ ρ' Hρ))
                (proj2 (tmden_EEqE t ρ ρ' Hρ))).
  - (* λ congruence *)
    intros a a' Ha.
    exact (IH (a, ρ) (a', ρ') (conj Ha Hρ)).
  - (* app congruence *)
    exact (IH1 ρ ρ' Hρ _ _ (IH2 ρ ρ' Hρ)).
  - (* suc congruence *)
    exact (f_equal S (IH ρ ρ' Hρ)).
  - (* rec congruence *)
    exact (natrec_EEq T _ _ _ _ _ _
             (IHz ρ ρ' Hρ) (IHs ρ ρ' Hρ) (IHn ρ ρ' Hρ)).
  - (* if congruence *)
    exact (if_EEq T _ _ _ _ _ _
             (IHc ρ ρ' Hρ) (IHt ρ ρ' Hρ) (IHf ρ ρ' Hρ)).
  - (* pair congruence *)
    exact (conj (IHa ρ ρ' Hρ) (IHb ρ ρ' Hρ)).
  - (* fst congruence *)
    exact (proj1 (IH ρ ρ' Hρ)).
  - (* snd congruence *)
    exact (proj2 (IH ρ ρ' Hρ)).
  - (* refl *)
    exact (tmden_EEqE t ρ ρ' Hρ).
  - (* sym *)
    exact (EEq_sym _ _ _ (IH ρ' ρ (EEqE_sym _ _ _ Hρ))).
  - (* trans *)
    exact (EEq_trans _ _ _ _ (IH1 ρ ρ' Hρ)
             (IH2 ρ' ρ' (EEqE_refl_r _ _ _ Hρ))).
Qed.

(** ** PER-trivial types (for the characteristic principles)

    A type is PER-trivial when all its inhabitants are interchangeable
    moves.  This is the semantic content of Bauer's [trivial_W]/[trivial_C]
    side conditions — but where his singleton formulation cannot prove
    arrows-into-singletons trivial without extensionality (his
    [singleton_power] remark), the PER formulation handles them by a
    one-line induction. *)

Fixpoint triv (T : ty) : bool :=
  match T with
  | tbase bUnit => true
  | tbase _ => false
  | tarr _ T2 => triv T2
  | tprod T1 T2 => triv T1 && triv T2
  end.

Lemma triv_EEq : forall T, triv T = true -> forall a b : tyden T, EEq T a b.
Proof.
  induction T as [b0 | T1 IH1 T2 IH2 | T1 IH1 T2 IH2]; simpl; intros H a b.
  - destruct b0; [discriminate | destruct a, b; reflexivity | discriminate].
  - intros x x' _; exact (IH2 H (a x) (b x')).
  - destruct (triv T1) eqn:E1; [| discriminate].
    split; [exact (IH1 eq_refl _ _) | exact (IH2 H _ _)].
Qed.
