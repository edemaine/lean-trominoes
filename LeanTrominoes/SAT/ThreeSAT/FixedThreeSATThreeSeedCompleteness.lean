/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Wang.WangPeriodicCNFSeedCompleteness
import LeanTrominoes.SAT.CNF.PeriodicCNFSeedSplittingFactors

/-! # Co-r.e.-complete finite prescriptions in one fixed local 3SAT-3 formula -/
noncomputable section
namespace LeanTrominoes.FixedThreeSATThreeSeed
open LeanWang

abbrev Variable := ThreeOccurrenceVariable (ThreeCNFVariable WangTile)

local instance : BEq Variable := instBEqOfDecidableEq
local instance : LawfulBEq Variable := by infer_instance

def splitFormula : PeriodicCNF (ThreeCNFVariable WangTile) :=
  PeriodicThreeCNF.formula WangPeriodicCNF.fixedFormula

def fixedFormula : PeriodicCNF Variable := PeriodicThreeSATThree.formula splitFormula

def reduction (seed : PeriodicCNF.Seed WangTile) : PeriodicCNF.Seed Variable :=
  PeriodicThreeSATThree.liftSeed splitFormula (PeriodicThreeCNF.liftSeed seed)

theorem reduction_primrec : Primrec reduction :=
  (PeriodicThreeSATThree.liftSeed_primrec.comp (Primrec.const splitFormula) Primrec.id).comp
    PeriodicThreeCNF.liftSeed_primrec

theorem reduction_correct (seed : PeriodicCNF.Seed WangTile) :
    WangPeriodicCNF.fixedFormula.Seeded seed ↔ fixedFormula.Seeded (reduction seed) :=
  (PeriodicThreeCNF.seeded_iff _ seed).trans
    (PeriodicThreeSATThree.seeded_iff_all splitFormula _)

theorem fixedFormula_isLocal : fixedFormula.IsLocal :=
  PeriodicThreeSATThree.formula_isLocal
    (PeriodicThreeCNF.formula_isLocal (WangPeriodicCNF.formula_isLocal _))

theorem fixedFormula_widthAtMostThree : fixedFormula.WidthAtMost 3 :=
  PeriodicThreeSATThree.formula_widthAtMostThree
    (PeriodicThreeCNF.formula_widthAtMostThree _)

theorem fixedFormula_occurrencesAtMostThree : fixedFormula.OccurrencesAtMost 3 := by
  exact PeriodicCNF.occurrencesAtMost_congr_beq
    _ _ (by infer_instance) (by infer_instance) 3 fixedFormula
    (PeriodicThreeSATThree.formula_occurrencesAtMostThree splitFormula)

theorem coREHard : CoREHard fixedFormula.Seeded := by
  intro A _ source hs
  obtain ⟨reduce,computable,correct⟩ := WangPeriodicCNF.fixedFormula_seeded_coREHard source hs
  refine ⟨reduction ∘ reduce,reduction_primrec.to_comp.comp computable,?_⟩
  intro a
  exact (correct a).trans (reduction_correct (reduce a))

theorem coREComplete : CoREComplete fixedFormula.Seeded :=
  ⟨PeriodicCNF.fixed_seeded_coRE fixedFormula,coREHard⟩

open Lean Elab Command in
run_cmd do
  let name := ``coREComplete
  let axioms ← Lean.collectAxioms name
  let extra := axioms.filter fun ax =>
    ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
  unless extra.isEmpty do throwError "{name} depends on unexpected axioms: {extra}"

end LeanTrominoes.FixedThreeSATThreeSeed
