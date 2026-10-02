/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicSubspaceTiling

/-! # Effective general subspace-tiling constraints and co-r.e. membership -/
namespace LeanTrominoes.PeriodicSubspaceTiling
open Computability
variable {G : Type} [AddCommGroup G] [DecidableEq G] [Primcodable G]

theorem records_primrec : Primrec (records G) := Primrec.snd

theorem candidates_primrec (neg_primrec : Primrec (fun z : G => -z)) : Primrec₂ (@candidates G _) := by
  have same : PrimrecRel fun (iq : Input G × Nat) (r : (Nat × Nat) × G) => r.1.2=iq.2 :=
    Primrec.eq.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.fst)
  have value : Primrec₂ fun (_iq : Input G × Nat) (r : (Nat × Nat) × G) =>
      some (r.1.1,-r.2) :=
    Primrec.option_some.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
      (neg_primrec.comp (Primrec.snd.comp Primrec.snd)))
  exact Primrec.listFilterMap (records_primrec.comp Primrec.fst)
    (Primrec.ite same value (Primrec.const none))

theorem formula_primrec (neg_primrec : Primrec (fun z : G => -z)) : Primrec (@formula G _ _) := by
  have cand := candidates_primrec neg_primrec
  have cover_pr : Primrec₂ (@cover G _) :=
    Primrec.list_map cand (Primrec.pair Primrec.snd (Primrec.const true))
  have pair_pr : Primrec₂ fun (ic : (Input G × Nat) × (Nat × G)) (e : Nat × G) =>
      if ic.2=e then [] else [[(ic.2,false),(e,false)]] := by
    have literal (f : ((Input G × Nat) × (Nat × G)) × (Nat × G) → Nat × G)
        (hf : Primrec f) : Primrec fun v => (f v,false) := Primrec.pair hf (Primrec.const false)
    have clause := Primrec.list_cons.comp (literal _ (Primrec.snd.comp Primrec.fst))
      (Primrec.list_cons.comp (literal _ Primrec.snd) (Primrec.const []))
    have output := Primrec.list_cons.comp clause (Primrec.const [])
    exact Primrec.ite (Primrec.eq.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
      (Primrec.const []) output
  have exclusions_pr : Primrec₂ (@exclusions G _ _) :=
    Primrec.list_flatMap cand
      (Primrec.list_flatMap (cand.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)) pair_pr)
  have main_pr : Primrec (fun input : Input G =>
      input.1.flatMap fun q => cover input q :: exclusions input q) :=
    Primrec.list_flatMap Primrec.fst (Primrec.list_cons.comp cover_pr exclusions_pr)
  have forbid_pr : Primrec (@forbidden G _) := by
    have inside : PrimrecRel fun (input : Input G) (r : (Nat × Nat) × G) => r.1.2 ∈ input.1 :=
      PeriodicCNF.FiniteSearch.mem_primrec.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.fst.comp Primrec.fst)
    have unit : Primrec₂ fun (_input : Input G) (r : (Nat × Nat) × G) =>
        [[((r.1.1,(0 : G)),false)]] := Primrec.list_cons.comp
      (Primrec.list_cons.comp
        (Primrec.pair (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.const (0 : G))) (Primrec.const false)) (Primrec.const [])) (Primrec.const [])
    exact Primrec.list_flatMap records_primrec (Primrec.ite inside (Primrec.const []) unit)
  exact Primrec.list_append.comp main_pr forbid_pr

/-- General finite quotient footprints belong to co-r.e.; no bounding-box
promise is needed for this half of Lemma 5.1. -/
theorem tileable_coRE (add_primrec : Primrec₂ (fun x y : G => x+y))
    (neg_primrec : Primrec (fun z : G => -z)) : LeanWang.CoREPred (@Tileable G _) := by
  have constraints := PeriodicConstraints.satisfiable_coRE add_primrec
  have preimage := LeanWang.REPred.comp constraints (formula_primrec neg_primrec).to_comp
  exact preimage.of_eq fun input => not_congr (tileable_iff_formula input).symm

/-- Coordinatewise integer addition is primitive recursive in every fixed dimension. -/
theorem lattice_add_primrec (d : Nat) : Primrec₂ (fun x y : Fin d → Int => x+y) := by
  apply Primrec.fin_curry.mpr
  exact Computability.int_add_primrec.comp (Primrec.fin_app.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
    (Primrec.fin_app.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)

theorem lattice_neg_primrec (d : Nat) : Primrec (fun z : Fin d → Int => -z) := by
  apply Primrec.fin_curry.mpr
  exact Computability.int_negate_primrec.comp Primrec.fin_app

/-- The co-r.e. membership clause of Lemma 5.1, in arbitrary dimension. -/
theorem lattice_tileable_coRE (d : Nat) :
    LeanWang.CoREPred (@Tileable (Fin d → Int) _) :=
  tileable_coRE (lattice_add_primrec d) (lattice_neg_primrec d)

end LeanTrominoes.PeriodicSubspaceTiling
