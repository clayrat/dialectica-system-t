(* Driver for the extracted Dialectica pipeline.

   Prints the normalized realizers of the showcase derivations from
   Dialectica.v / Realizer.v, each produced by the *extracted* [wit] and
   [norm] running in OCaml at module load — an end-to-end check that the
   extracted pipeline works, not just that it compiles.  It then replays the
   closed Dialectica games (matrix · witness · counter): by the Rocq theorem
   [soundness_syntactic] every one must normalize to [true], and the driver
   fails loudly if the extracted code disagrees.

   Normal forms are shown with de Bruijn indices ([#0] is the innermost bound
   variable), runs of successors collapsed to integers, and [λ.] for binders.
   (The printer is the one from nbe-system-t/extraction/main.ml.) *)

open Dialectica

let rec var_idx : var -> int = function
  | Vz _ -> 0
  | Vs (_, _, _, y) -> 1 + var_idx y

let rec pp_nf (n : nf) : string =
  let rec count k = function
    | Nsuc (_, v) -> count (k + 1) v
    | base -> (k, base)
  in
  match n with
  | Nzero _ -> "0"
  | Nsuc _ ->
    let k, base = count 0 n in
    (match base with
     | Nzero _ -> string_of_int k
     | Nne (_, _, u) -> Printf.sprintf "%d + %s" k (pp_ne u)
     | other -> Printf.sprintf "%d + %s" k (pp_nf other))
  | Nunit _ -> "tt"
  | Ntrue _ -> "true"
  | Nfalse _ -> "false"
  | Nne (_, _, u) -> pp_ne u
  | Nlam (_, _, _, v) -> "λ. " ^ pp_nf v
  | Npair (_, _, _, v1, v2) -> "(" ^ pp_nf v1 ^ ", " ^ pp_nf v2 ^ ")"

and pp_ne (u : ne) : string =
  match u with
  | Nvar (_, _, x) -> "#" ^ string_of_int (var_idx x)
  | Napp (_, _, _, u, v) -> "(" ^ pp_ne u ^ " " ^ pp_nf v ^ ")"
  | Nrec (_, _, z, s, u) ->
    Printf.sprintf "rec(%s, %s, %s)" (pp_nf z) (pp_nf s) (pp_ne u)
  | Nif (_, _, t, f, u) ->
    Printf.sprintf "if %s then %s else %s" (pp_ne u) (pp_nf t) (pp_nf f)
  | Nfst (_, _, _, u) -> "fst " ^ pp_ne u
  | Nsnd (_, _, _, u) -> "snd " ^ pp_ne u

let () =
  let show name nf expected =
    Printf.printf "  %-28s  ~>  %-24s  (expect %s)\n" name (pp_nf nf) expected
  in
  print_endline
    "Dialectica realizers (wit + NbE norm, extracted from Rocq):";
  print_newline ();
  show "|- ∃y. y = 2" real_two "(2, tt)";
  show "|- ∀x ∃y. y = S x" real_succ "λ. (1 + #0, tt)";
  show "|- ∃y. y = 0   [Markov]" real_markov "(0, tt)";
  show "|- ∀x. x + 0 = x   [ind]" real_plus0 "λ. rec(tt, ..., #0)";
  print_newline ();
  print_endline
    "Closed Dialectica games, replayed by the extracted normalizer";
  print_endline
    "(soundness_syntactic: each matrix · witness · counter must be true):";
  print_newline ();
  let check name nf =
    Printf.printf "  %-28s  ~>  %s\n" name (pp_nf nf);
    match nf with
    | Ntrue _ -> ()
    | _ -> failwith ("matrix check failed: " ^ name)
  in
  check "|∃y. y = 2| @ tt" chk_two;
  check "|∃y. y = 0| @ tt" chk_markov;
  check "|∀x. x + 0 = x| @ (5, tt)" chk_plus0
