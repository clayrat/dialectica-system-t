(* Hand-written, Obj.magic-free Dialectica pipeline for System T — REFERENCE ONLY.

   This is to extraction/dialectica.ml what nbe-system-t/reference/nbe_native.ml
   is to its nbe.ml: the same algorithms, written as an OCaml programmer would.
   It follows the extracted file's layout — NbE core, substitution kit, HA
   formulas and derivations, the W/C translation, the internal matrix [dia_t],
   the realizer combinators, the proof translation [wit] — but sheds the
   artefacts of extracting dependently typed code:

   - Contexts are erased entirely (the NbE core keeps lengths, the syntax
     keeps nothing); type annotations survive only where they are load-bearing
     (Tvar / Trec / Tif, and the type-directed reify/reflect).
   - The [tcast] transports are gone: W/C-invariance under renaming and
     substitution ("only the atoms change, and atoms contribute TUnit") is
     *definitional* once the syntax is context-free, so [w_ty (psub1 q t)]
     and [w_ty q] are literally the same value.
   - The [Prop] content — [defeq] evidence in [Ax_conv], the [wtriv]/[ctriv]
     side conditions of [Ax_markov]/[Ax_ip] — was already erased by
     extraction and stays gone; the [proof] variant below keeps exactly the
     informative fields of the Rocq constructors.
   - Renamings and substitutions are functions on variables, lifted under
     binders (the function-space reading of NbE's Subst.v), instead of the
     extracted first-order encodings threading context arguments.

   The NbE core (syntax / value / eval / reify / reflect / norm and the
   printer) is loaded from nbe-system-t/reference/nbe_native.ml; see its
   header and extraction/DESIGN.md there for why [value] is one variant with
   [assert false] arms, and for the trust boundary (input well-typedness is
   assumed, not checked — wrong input gives wrong output or a crash).

   The driver at the bottom replays the Rocq-side theorems on the showcase
   derivations (realizer_two/succ/markov/plus0 and the syn_* checks in
   theories/Realizer.v) and asserts the same answers.

   Run it:  ocaml reference/dialectica_native.ml *)

(* Load the submodule's hand-written System T implementation as a module.
   [#mod_use] keeps this reference file directly runnable by the OCaml
   interpreter without introducing a separate build step. *)
#mod_use "nbe-system-t/reference/nbe_native.ml";;
open Nbe_native

(* Application as a left-associative infix, mirroring the Rocq notation [·]. *)
let ( $. ) u v = Tapp (u, v)

(* Typed de Bruijn references (the annotation is the variable's type). *)
let v0 t = Tvar (t, 0)
let v1 t = Tvar (t, 1)
let v2 t = Tvar (t, 2)
let v3 t = Tvar (t, 3)
let v4 t = Tvar (t, 4)

(* ===== Renaming and substitution (Terms.v / NbE's Subst.v, as functions) === *)

type ren = var -> var
type sub = ty -> var -> tm

let ren_lift (r : ren) (x : var) : var =
  if x = 0 then 0 else 1 + r (x - 1)

let rec tm_ren (r : ren) : tm -> tm = function
  | Tzero -> Tzero
  | Tsuc t -> Tsuc (tm_ren r t)
  | Trec (ty, z, s, n) -> Trec (ty, tm_ren r z, tm_ren r s, tm_ren r n)
  | Tunit -> Tunit
  | Ttrue -> Ttrue
  | Tfalse -> Tfalse
  | Tif (ty, c, t, f) -> Tif (ty, tm_ren r c, tm_ren r t, tm_ren r f)
  | Tvar (t, x) -> Tvar (t, r x)
  | Tlam t -> Tlam (tm_ren (ren_lift r) t)
  | Tapp (u, v) -> Tapp (tm_ren r u, tm_ren r v)
  | Tpair (a, b) -> Tpair (tm_ren r a, tm_ren r b)
  | Tfst t -> Tfst (tm_ren r t)
  | Tsnd t -> Tsnd (tm_ren r t)

let wk1 t = tm_ren (( + ) 1) t
let wk2 t = wk1 (wk1 t)

let sub_lift (s : sub) : sub = fun t x ->
  if x = 0 then Tvar (t, 0) else wk1 (s t (x - 1))

let rec tm_sub (s : sub) : tm -> tm = function
  | Tzero -> Tzero
  | Tsuc t -> Tsuc (tm_sub s t)
  | Trec (ty, z, st, n) -> Trec (ty, tm_sub s z, tm_sub s st, tm_sub s n)
  | Tunit -> Tunit
  | Ttrue -> Ttrue
  | Tfalse -> Tfalse
  | Tif (ty, c, t, f) -> Tif (ty, tm_sub s c, tm_sub s t, tm_sub s f)
  | Tvar (t, x) -> s t x
  | Tlam t -> Tlam (tm_sub (sub_lift s) t)
  | Tapp (u, v) -> Tapp (tm_sub s u, tm_sub s v)
  | Tpair (a, b) -> Tpair (tm_sub s a, tm_sub s b)
  | Tfst t -> Tfst (tm_sub s t)
  | Tsnd t -> Tsnd (tm_sub s t)

let vs_add d x = max 0 d + x

(* Substitute [n] for the head variable, sending the remaining variables [d]
   binders deeper — Terms.v's [sub_at0] ([sub1] is the [d = 0] instance). *)
let sub_at0 (d : int) (n : tm) : sub = fun t x ->
  if x = 0 then n else Tvar (t, vs_add d (x - 1))

let sub1 (n : tm) : sub = sub_at0 0 n

(* The head-successor substitution [x0 ↦ S x0] behind [psucc]. *)
let sub_succ : sub = fun t x ->
  if x = 0 then Tsuc (Tvar (TN, 0)) else Tvar (t, x)

(* ===== The System T kit (Terms.v) ===== *)

let tandb a b = Tif (TBool, a, b, Tfalse)
let timplb a b = Tif (TBool, a, b, Ttrue)
let tnegb a = Tif (TBool, a, Tfalse, Ttrue)

let rec tdefault : ty -> tm = function
  | TN -> Tzero
  | TUnit -> Tunit
  | TBool -> Ttrue
  | Tarr (_, b) -> Tlam (tdefault b)
  | Tprod (a, b) -> Tpair (tdefault a, tdefault b)

let rec numeral n = if n <= 0 then Tzero else Tsuc (numeral (n - 1))

(* eqb = λm. rec iszero (λm' r. λn. rec false (λn' _. r n') n) m *)
let tiszero = Tlam (Trec (TBool, Ttrue, Tlam (Tlam Tfalse), v0 TN))

let teqb =
  Tlam (Trec (Tarr (TN, TBool),
              tiszero,
              Tlam (Tlam (Tlam
                (Trec (TBool,
                       Tfalse,
                       Tlam (Tlam (v3 (Tarr (TN, TBool)) $. v1 TN)),
                       v0 TN)))),
              v0 TN))

(* plus = λm n. rec n (λm' r. S r) m — recursing on the *first* argument, so
   [m + 0] is stuck and [∀x. x + 0 = x] genuinely needs induction. *)
let tplus =
  Tlam (Tlam (Trec (TN, v0 TN, Tlam (Tlam (Tsuc (v0 TN))), v1 TN)))

(* ===== HA formulas and derivations (HA.v) ===== *)

type prp =
  | PAtom of tm                      (* decidable atom: a Bool-valued program *)
  | PAnd of prp * prp
  | POr of prp * prp
  | PImp of prp * prp
  | PAll of prp                      (* binds a fresh tN variable *)
  | PEx of prp

let rec prp_ren (r : ren) : prp -> prp = function
  | PAtom b -> PAtom (tm_ren r b)
  | PAnd (a, b) -> PAnd (prp_ren r a, prp_ren r b)
  | POr (a, b) -> POr (prp_ren r a, prp_ren r b)
  | PImp (a, b) -> PImp (prp_ren r a, prp_ren r b)
  | PAll a -> PAll (prp_ren (ren_lift r) a)
  | PEx a -> PEx (prp_ren (ren_lift r) a)

let rec prp_sub (s : sub) : prp -> prp = function
  | PAtom b -> PAtom (tm_sub s b)
  | PAnd (a, b) -> PAnd (prp_sub s a, prp_sub s b)
  | POr (a, b) -> POr (prp_sub s a, prp_sub s b)
  | PImp (a, b) -> PImp (prp_sub s a, prp_sub s b)
  | PAll a -> PAll (prp_sub (sub_lift s) a)
  | PEx a -> PEx (prp_sub (sub_lift s) a)

let pwk a = prp_ren (( + ) 1) a
let psub1 a t = prp_sub (sub1 t) a
let psucc a = prp_sub sub_succ a

let p_true = PAtom Ttrue
let p_false = PAtom Tfalse
let pnot a = PImp (a, p_false)
let eqb t s = teqb $. t $. s
let peq t s = PAtom (eqb t s)

(* Derivations. Each constructor keeps only the fields consumed by witness
   extraction. Contexts, formula labels recoverable only from the typing
   judgment, terms attached to computationally trivial axioms, and Prop
   content are erased. Nothing here checks that a [proof] value is well-formed:
   like term well-typedness, derivation well-formedness is trusted input. *)
type proof =
  | Ax_true
  | Ax_mp of proof * proof                          (* ⊢ P⊃Q, P => Q *)
  | Ax_chain of prp * prp * proof * proof           (* P, R; Q is erased *)
  | Ax_or_contr of prp                              (* P∨P ⊃ P *)
  | Ax_and_contr of prp                             (* P ⊃ P∧P *)
  | Ax_or_inl of prp * prp                          (* P ⊃ P∨Q *)
  | Ax_and_eliml of prp * prp                       (* P∧Q ⊃ P *)
  | Ax_or_comm of prp * prp                         (* P∨Q ⊃ Q∨P *)
  | Ax_and_comm of prp * prp                        (* P∧Q ⊃ Q∧P *)
  | Ax_or_distr of prp * prp * prp * proof          (* P⊃Q => R∨P ⊃ R∨Q *)
  | Ax_cur of prp * prp * prp * proof               (* P∧Q⊃R => P⊃(Q⊃R) *)
  | Ax_uncur of prp * prp * prp * proof             (* P⊃(Q⊃R) => P∧Q⊃R *)
  | Ax_exfalso of prp                               (* ⊥ ⊃ P *)
  | Ax_all_intro of prp * prp * proof               (* P, Q ⊢ pwk P ⊃ Q => P ⊃ ∀Q *)
  | Ax_all_elim of prp * tm                         (* ∀Q ⊃ Q[t] *)
  | Ax_ex_intro of prp * tm                         (* Q[t] ⊃ ∃Q *)
  | Ax_ex_elim of prp * prp * proof                 (* P, Q ⊢ Q ⊃ pwk P => ∃Q ⊃ P *)
  | Ax_eq_refl                                      (* t = t *)
  | Ax_leibniz of prp                               (* t = s ⊃ Q[t] ⊃ Q[s] *)
  | Ax_succ_nonzero                                 (* ¬(S t = 0) *)
  | Ax_succ_inj                                     (* S t = S s ⊃ t = s *)
  | Ax_ind of prp                                   (* Q[0] ∧ ∀(Q ⊃ Q[S]) ⊃ ∀Q *)
  | Ax_conv of proof                                (* atom conversion *)
  | Ax_markov of prp                                (* ¬∀¬P ⊃ ∃P *)
  | Ax_ip of prp * prp                              (* (∀P ⊃ ∃Q) ⊃ ∃(pwk(∀P) ⊃ Q) *)

(* Derived rules (the ones the examples use). *)
let d_id p = Ax_chain (p, p, Ax_and_contr p, Ax_and_eliml (p, p))
let d_K p q = Ax_cur (p, q, p, Ax_and_eliml (p, q))

let d_swap p q r u =
  Ax_cur (q, p, r,
          Ax_chain (PAnd (q, p), r,
                    Ax_and_comm (q, p), Ax_uncur (p, q, r, u)))

let d_dni p q a =
  Ax_mp (d_swap (PImp (p, q)) p q (d_id (PImp (p, q))), a)

let d_and_intro p q = Ax_cur (p, q, PAnd (p, q), d_id (PAnd (p, q)))

let d_pair p q a b =
  Ax_mp (Ax_mp (d_and_intro p q, a), b)

let d_gen q u =
  Ax_mp (Ax_all_intro (p_true, q,
           Ax_mp (d_K q (pwk p_true), u)),
         Ax_true)

(* ===== The Dialectica translation (Dialectica.v) ===== *)

(* Witness and counter types, exactly Gödel's.  They only look at the shape
   of the formula, so — with the context gone — invariance under renaming and
   substitution is definitional and no transports are ever needed. *)
let rec w_ty : prp -> ty = function
  | PAtom _ -> TUnit
  | PAnd (b, d) -> Tprod (w_ty b, w_ty d)
  | POr (b, d) -> Tprod (TBool, Tprod (w_ty b, w_ty d))
  | PImp (b, d) -> Tprod (Tarr (w_ty b, w_ty d),
                          Tarr (w_ty b, Tarr (c_ty d, c_ty b)))
  | PAll b -> Tarr (TN, w_ty b)
  | PEx b -> Tprod (TN, w_ty b)
and c_ty : prp -> ty = function
  | PAtom _ -> TUnit
  | PAnd (b, d) -> Tprod (c_ty b, c_ty d)
  | POr (b, d) -> Tprod (c_ty b, c_ty d)
  | PImp (b, d) -> Tprod (w_ty b, c_ty d)
  | PAll b -> Tprod (TN, c_ty b)
  | PEx b -> c_ty b

(* The quantifier-free matrix |A|(w, c), as a System T program of type
   W A ⇒ C A ⇒ Bool — the realizers of contraction and induction run it. *)
let rec dia_t (a : prp) : tm =
  let wa = w_ty a and ca = c_ty a in
  match a with
  | PAtom b -> Tlam (Tlam (wk2 b))
  | PAnd (b, d) ->
    Tlam (Tlam (tandb
      (wk2 (dia_t b) $. Tfst (v1 wa) $. Tfst (v0 ca))
      (wk2 (dia_t d) $. Tsnd (v1 wa) $. Tsnd (v0 ca))))
  | POr (b, d) ->
    Tlam (Tlam (Tif (TBool, Tfst (v1 wa),
      wk2 (dia_t b) $. Tfst (Tsnd (v1 wa)) $. Tfst (v0 ca),
      wk2 (dia_t d) $. Tsnd (Tsnd (v1 wa)) $. Tsnd (v0 ca))))
  | PImp (b, d) ->
    Tlam (Tlam (timplb
      (wk2 (dia_t b) $. Tfst (v0 ca)
         $. (Tsnd (v1 wa) $. Tfst (v0 ca) $. Tsnd (v0 ca)))
      (wk2 (dia_t d) $. (Tfst (v1 wa) $. Tfst (v0 ca)) $. Tsnd (v0 ca))))
  | PAll b ->
    Tlam (Tlam (tm_sub (sub_at0 2 (Tfst (v0 ca))) (dia_t b)
      $. (v1 wa $. Tfst (v0 ca)) $. Tsnd (v0 ca)))
  | PEx b ->
    Tlam (Tlam (tm_sub (sub_at0 2 (Tfst (v1 wa))) (dia_t b)
      $. Tsnd (v1 wa) $. v0 ca))

(* ----- Realizer combinators, one per proof rule (the r_ definitions of
   Dialectica.v).  A witness of an implication is a pair (forward map on
   witnesses, backward map on counters); [Tlam] is unannotated, so the formula
   arguments are only consumed for variable annotations and the
   [tdefault]/[dia_t] calls. ----- *)

let r_mp u a = Tfst u $. a

let r_chain p r u v =
  Tpair (Tlam (Tfst (wk1 v) $. (Tfst (wk1 u) $. v0 (w_ty p))),
         Tlam (Tlam (Tsnd (wk2 u) $. v1 (w_ty p)
           $. (Tsnd (wk2 v) $. (Tfst (wk2 u) $. v1 (w_ty p)) $. v0 (c_ty r)))))

let r_or_contr p =
  let w_or = w_ty (POr (p, p)) in
  Tpair (Tlam (Tif (w_ty p, Tfst (v0 w_or),
                    Tfst (Tsnd (v0 w_or)), Tsnd (Tsnd (v0 w_or)))),
         Tlam (Tlam (Tpair (v0 (c_ty p), v0 (c_ty p)))))

let r_and_contr p =
  let c_and = c_ty (PAnd (p, p)) in
  Tpair (Tlam (Tpair (v0 (w_ty p), v0 (w_ty p))),
         Tlam (Tlam (Tif (c_ty p,
                          wk2 (dia_t p) $. v1 (w_ty p) $. Tfst (v0 c_and),
                          Tsnd (v0 c_and), Tfst (v0 c_and)))))

let r_or_inl p q =
  let c_or = c_ty (POr (p, q)) in
  Tpair (Tlam (Tpair (Ttrue, Tpair (v0 (w_ty p), tdefault (w_ty q)))),
         Tlam (Tlam (Tfst (v0 c_or))))

let r_and_eliml p q =
  let w_and = w_ty (PAnd (p, q)) in
  Tpair (Tlam (Tfst (v0 w_and)),
         Tlam (Tlam (Tpair (v0 (c_ty p), tdefault (c_ty q)))))

let r_or_comm p q =
  let w_or = w_ty (POr (p, q)) and c_or' = c_ty (POr (q, p)) in
  Tpair (Tlam (Tpair (tnegb (Tfst (v0 w_or)),
                      Tpair (Tsnd (Tsnd (v0 w_or)), Tfst (Tsnd (v0 w_or))))),
         Tlam (Tlam (Tpair (Tsnd (v0 c_or'), Tfst (v0 c_or')))))

let r_and_comm p q =
  let w_and = w_ty (PAnd (p, q)) and c_and' = c_ty (PAnd (q, p)) in
  Tpair (Tlam (Tpair (Tsnd (v0 w_and), Tfst (v0 w_and))),
         Tlam (Tlam (Tpair (Tsnd (v0 c_and'), Tfst (v0 c_and')))))

let r_or_distr p q r u =
  let w_rp = w_ty (POr (r, p)) and c_rq = c_ty (POr (r, q)) in
  Tpair (Tlam (Tpair (Tfst (v0 w_rp),
                      Tpair (Tfst (Tsnd (v0 w_rp)),
                             Tfst (wk1 u) $. Tsnd (Tsnd (v0 w_rp))))),
         Tlam (Tlam (Tpair (Tfst (v0 c_rq),
                            Tsnd (wk2 u) $. Tsnd (Tsnd (v1 w_rp))
                              $. Tsnd (v0 c_rq)))))

let r_cur p q r u =
  let c_qr = c_ty (PImp (q, r)) in
  Tpair
    (Tlam (Tpair
       (Tlam (Tfst (wk2 u) $. Tpair (v1 (w_ty p), v0 (w_ty q))),
       Tlam (Tlam (Tsnd (Tsnd (wk1 (wk2 u))
         $. Tpair (v2 (w_ty p), v1 (w_ty q)) $. v0 (c_ty r)))))),
     Tlam (Tlam (Tfst (Tsnd (wk2 u)
       $. Tpair (v1 (w_ty p), Tfst (v0 c_qr)) $. Tsnd (v0 c_qr)))))

let r_uncur p q r u =
  let w_pq = w_ty (PAnd (p, q)) in
  Tpair
    (Tlam (Tfst (Tfst (wk1 u) $. Tfst (v0 w_pq)) $. Tsnd (v0 w_pq)),
     Tlam (Tlam (Tpair
       (Tsnd (wk2 u) $. Tfst (v1 w_pq)
          $. Tpair (Tsnd (v1 w_pq), v0 (c_ty r)),
        Tsnd (Tfst (wk2 u) $. Tfst (v1 w_pq))
          $. Tsnd (v1 w_pq) $. v0 (c_ty r)))))

let r_exfalso p =
  Tpair (Tlam (tdefault (w_ty p)), Tlam (Tlam Tunit))

(* u :  W (pwk P ⊃ Q)  one tN binder up;  its head variable is instantiated
   under the new λs, the rest pushed past them — [sub_at0], no casts. *)
let r_all_intro p q u =
  let c_all = c_ty (PAll q) in
  Tpair
    (Tlam (Tlam (Tfst (tm_sub (sub_at0 2 (v0 TN)) u) $. v1 (w_ty p))),
     Tlam (Tlam (Tsnd (tm_sub (sub_at0 2 (Tfst (v0 c_all))) u)
       $. v1 (w_ty p) $. Tsnd (v0 c_all))))

let r_all_elim q t =
  let w_all = w_ty (PAll q) in
  Tpair (Tlam (v0 w_all $. wk1 t),
         Tlam (Tlam (Tpair (wk2 t, v0 (c_ty q)))))

let r_ex_intro q t =
  Tpair (Tlam (Tpair (wk1 t, v0 (w_ty q))),
         Tlam (Tlam (v0 (c_ty q))))

let r_ex_elim p q u =
  let w_ex = w_ty (PEx q) in
  Tpair
    (Tlam (Tfst (tm_sub (sub_at0 1 (Tfst (v0 w_ex))) u) $. Tsnd (v0 w_ex)),
     Tlam (Tlam (Tsnd (tm_sub (sub_at0 2 (Tfst (v1 w_ex))) u)
       $. Tsnd (v1 w_ex) $. v0 (c_ty p))))

(* All atoms have trivial witnesses, so Leibniz is transport — and with the
   casts gone it is literally the identity on both sides. *)
let r_leibniz q =
  Tpair (Tlam (Tpair (Tlam (v0 (w_ty q)), Tlam (Tlam (v0 (c_ty q))))),
         Tlam (Tlam Tunit))

let r_atom_imp = Tpair (Tlam Tunit, Tlam (Tlam Tunit))

(* Induction: forward is primitive recursion on the step witnesses; backward
   is Gödel's downward counterexample search, one recursor computing the pair
   (w_k, g_k) — see the long comment on [r_ind] in Dialectica.v. *)
let r_ind q =
  let wq = w_ty q and cq = c_ty q in
  let w_prem = Tprod (wq, Tarr (TN, Tprod (Tarr (wq, wq),
                                           Tarr (wq, Tarr (cq, cq))))) in
  let c_prem = Tprod (cq, Tprod (TN, Tprod (wq, cq))) in
  let c_all = Tprod (TN, cq) in
  let motive = Tprod (wq, Tarr (cq, c_prem)) in
  let fwd =
    Tlam (Tlam (Trec (wq,
      Tfst (v1 w_prem),
      Tlam (Tlam (Tfst (Tsnd (v3 w_prem) $. v1 TN) $. v0 wq)),
      v0 TN)))
  in
  (* (w_0, g_0):  g_0 c = (c, dummy blame) *)
  let z =
    Tpair (Tfst (v1 w_prem),
           Tlam (Tpair (v0 cq,
                        Tpair (Tzero, Tpair (tdefault wq, tdefault cq)))))
  in
  (* λk (w_k, g_k). (w_{k+1}, g_{k+1}):  g_{k+1} c tests the matrix at k and
     either blames step k or recurses into g_k. *)
  let s =
    let g_step =
      Tlam (
        let c = v0 cq in
        let c' = Tsnd (Tsnd (v4 w_prem) $. v2 TN) $. Tfst (v1 motive) $. c in
        Tif (c_prem,
             tm_sub (sub_at0 5 (v2 TN)) (dia_t q) $. Tfst (v1 motive) $. c',
             Tpair (tdefault cq, Tpair (v2 TN, Tpair (Tfst (v1 motive), c))),
             Tsnd (v1 motive) $. c'))
    in
    Tlam (Tlam (Tpair
      (Tfst (Tsnd (v3 w_prem) $. v1 TN) $. Tfst (v0 motive),
       g_step)))
  in
  let bwd =
    Tlam (Tlam (Tsnd (Trec (motive, z, s, Tfst (v0 c_all)))
      $. Tsnd (v0 c_all)))
  in
  Tpair (fwd, bwd)

(* Markov: the counter-half of the ¬∀¬P witness, fed the canonical family,
   yields the existential index; every other move is a default (the
   wtriv/ctriv side conditions make defaults as good as any move). *)
let r_markov p =
  let w_h = w_ty (pnot (PAll (pnot p))) in
  let w_fam = w_ty (PAll (pnot p)) in
  Tpair
    (Tlam (Tpair
       (Tfst (Tsnd (v0 w_h) $. tdefault w_fam $. Tunit),
        tdefault (w_ty p))),
     Tlam (Tlam (Tpair (tdefault w_fam, Tunit))))

(* Independence of Premise: project the premise witness at the canonical
   ∀-family; the Rocq version's one tcast is gone. *)
let r_ip p q =
  let w_imp = w_ty (PImp (PAll p, PEx q)) in
  let w_all = w_ty (PAll p) in
  let c_ex = c_ty (PEx (PImp (pwk (PAll p), q))) in
  Tpair
    (Tlam (Tpair
       (Tfst (Tfst (v0 w_imp) $. tdefault w_all),
        Tpair
          (Tlam (Tsnd (Tfst (v1 w_imp) $. tdefault w_all)),
           Tlam (Tlam (Tsnd (v2 w_imp) $. tdefault w_all $. v0 (c_ty q)))))),
     Tlam (Tlam (Tpair (tdefault w_all, Tsnd (v0 c_ex)))))

(* The proof translation: dispatch each rule to its combinator. *)
let rec wit : proof -> tm = function
  | Ax_true -> Tunit
  | Ax_mp (u, a) -> r_mp (wit u) (wit a)
  | Ax_chain (p, r, u, v) -> r_chain p r (wit u) (wit v)
  | Ax_or_contr p -> r_or_contr p
  | Ax_and_contr p -> r_and_contr p
  | Ax_or_inl (p, q) -> r_or_inl p q
  | Ax_and_eliml (p, q) -> r_and_eliml p q
  | Ax_or_comm (p, q) -> r_or_comm p q
  | Ax_and_comm (p, q) -> r_and_comm p q
  | Ax_or_distr (p, q, r, u) -> r_or_distr p q r (wit u)
  | Ax_cur (p, q, r, u) -> r_cur p q r (wit u)
  | Ax_uncur (p, q, r, u) -> r_uncur p q r (wit u)
  | Ax_exfalso p -> r_exfalso p
  | Ax_all_intro (p, q, u) -> r_all_intro p q (wit u)
  | Ax_all_elim (q, t) -> r_all_elim q t
  | Ax_ex_intro (q, t) -> r_ex_intro q t
  | Ax_ex_elim (p, q, u) -> r_ex_elim p q (wit u)
  | Ax_eq_refl -> Tunit
  | Ax_leibniz q -> r_leibniz q
  | Ax_succ_nonzero -> r_atom_imp
  | Ax_succ_inj -> r_atom_imp
  | Ax_ind q -> r_ind q
  | Ax_conv d -> wit d
  | Ax_markov p -> r_markov p
  | Ax_ip (p, q) -> r_ip p q

let realizer (a : prp) (d : proof) : nf = norm 0 (w_ty a) (wit d)

(* ===== The showcase derivations (Dialectica.v / Realizer.v) ===== *)

let x0 = v0 TN
let x1 = v1 TN

(* ⊢ ∃y. y = 2, by ∃-introduction at 2. *)
let q_two = peq x0 (numeral 2)
let ex_two =
  Ax_mp (Ax_ex_intro (q_two, numeral 2), Ax_eq_refl)

(* ⊢ ∀x ∃y. y = S x — the realizer is the successor program. *)
let q_succ = peq x0 (Tsuc x1)
let ex_succ =
  d_gen (PEx q_succ)
    (Ax_mp (Ax_ex_intro (q_succ, Tsuc x0), Ax_eq_refl))

(* ⊢ ∃y. y = 0 the non-constructive way: refute ∀y.¬(y = 0) at 0, then
   conclude by Markov's principle.  Normalization still finds the witness. *)
let p_mp = peq x0 Tzero
let mp_notallnot =
  Ax_chain (PAll (pnot p_mp), p_false,
            Ax_all_elim (pnot p_mp, Tzero),
            d_dni (peq Tzero Tzero) p_false Ax_eq_refl)
let mp_ex =
  Ax_mp (Ax_markov p_mp, mp_notallnot)

(* ⊢ ∀x. x + 0 = x by induction (plus recurses on its first argument).
   Base and the step's computation fact are reflexivity instances converted
   along the defining equations of plus ([Ax_conv]); the step routes through
   Leibniz at the motive [S x + 0 = S z]. *)
let plus m n = tplus $. m $. n
let p_plus0 = peq (plus x0 Tzero) x0
let q_step = peq (plus (Tsuc x1) Tzero) (Tsuc x0)
let t_plus0 = plus x0 Tzero

let plus0_base =
  Ax_conv Ax_eq_refl

let plus0_step =
  d_gen (PImp (p_plus0, psucc p_plus0))
    (Ax_mp
       (d_swap (peq t_plus0 x0) (psub1 q_step t_plus0) (psub1 q_step x0)
          (Ax_leibniz q_step),
        Ax_conv Ax_eq_refl))

let plus0 =
  let base_f = psub1 p_plus0 Tzero in
  let step_f = PAll (PImp (p_plus0, psucc p_plus0)) in
  Ax_mp (Ax_ind p_plus0, d_pair base_f step_f plus0_base plus0_step)

(* ===== Driver (using the pretty-printer from nbe_native.ml) ===== *)

let () =
  (* Realizers, asserted against the Rocq-side normal forms
     (realizer_two / realizer_succ / realizer_markov / realizer_plus0). *)
  let show name a d expected =
    let n = realizer a d in
    Printf.printf "  %-26s ~> %-24s (expect %s)\n" name (pp_nf n) expected;
    n
  in
  print_endline "Native (Obj.magic-free) Dialectica realizers:\n";
  assert (show "|- \xe2\x88\x83y. y = 2" (PEx q_two) ex_two "(2, tt)"
          = Npair (Nsuc (Nsuc Nzero), Nunit));
  assert (show "|- \xe2\x88\x80x \xe2\x88\x83y. y = S x" (PAll (PEx q_succ)) ex_succ
            "\xce\xbb. (1 + #0, tt)"
          = Nlam (Npair (Nsuc (Nne (Nvar 0)), Nunit)));
  assert (show "|- \xe2\x88\x83y. y = 0  [Markov]" (PEx p_mp) mp_ex "(0, tt)"
          = Npair (Nzero, Nunit));
  assert (show "|- \xe2\x88\x80x. x + 0 = x  [ind]" (PAll p_plus0) plus0
            "\xce\xbb. rec(tt, ..., #0)"
          = Nlam (Nne (Nrec (Nunit, Nlam (Nlam Nunit), Nvar 0))));
  (* Closed Dialectica games: matrix · witness · counter must normalize to
     true (the syn_* instances of soundness_syntactic). *)
  print_endline "\nClosed games (matrix \xc2\xb7 witness \xc2\xb7 counter):\n";
  let check name a d counter =
    let n = norm 0 TBool (dia_t a $. wit d $. counter) in
    Printf.printf "  %-26s ~> %s\n" name (pp_nf n);
    assert (n = Ntrue)
  in
  check "|\xe2\x88\x83y. y = 2| @ tt" (PEx q_two) ex_two Tunit;
  check "|\xe2\x88\x83y. y = 0| @ tt" (PEx p_mp) mp_ex Tunit;
  check "|\xe2\x88\x80x. x + 0 = x| @ (5, tt)" (PAll p_plus0) plus0
        (Tpair (numeral 5, Tunit))
