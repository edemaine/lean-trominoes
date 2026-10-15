/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Wang.FixedWangNormalizedSeedDecoder
import LeanTrominoes.Graphs.Orientation.NormalizedOrientationQuarterMargin
import LeanTrominoes.Tiling.Wang.WangPeriodicCNFQuarterDecoder

/-! # A prescribed Q decodes a valid universal Wang quarter-plane -/
noncomputable section
namespace LeanTrominoes.FixedPolyominoSeed
open PlusRefinement Gadget

def windowRadius : Nat := Classical.choose FixedWangNormalizedSeedDecoder.uniform_window
def baseline (n : Nat) : Cell := NormalizedOrientation.AsCNF.quarterBaseline n windowRadius

def wangAssignment (n : Nat) (ps : Set (Placement Bool)) : LeanWang.WangTile → Cell → Bool :=
  fun tile c => PeriodicCNF.SignedDecoder.decode FixedWangNormalizedSeedDecoder.read
    (KeyedPeriodicComplement.ShiftedGadgetReadout.assignment FixedNormalizedOrientationSeed.fixedDrawing (9,3) ps)
    tile (Cell.add (baseline n) c)

theorem quarter_satisfies {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : KeyedPeriodicComplement.AdmissibleHoles n holes)
    (carrier : KeyedPeriodicComplement.holesRegion n holes = region
      (KeyedPeriodicComplement.ShiftedGadgetReadout.original FixedNormalizedOrientationSeed.fixedDrawing (9,3)))
    (ps : Set (Placement Bool))
    (tiling : IsTiling (pairTiles bumpy (KeyedPeriodicComplement.tile n holes)) Set.univ ps)
    (seed : KeyedPeriodicComplement.referencePlacement ∈ ps) :
    WangPeriodicCNF.QuarterSatisfies FixedMachineWangSeed.PlaneExtension.universalPlanePalette (wangAssignment n ps) := by
  intro point clause member
  have localRule := Classical.choose_spec FixedWangNormalizedSeedDecoder.uniform_window
  have forced := localRule
    (KeyedPeriodicComplement.ShiftedGadgetReadout.assignment FixedNormalizedOrientationSeed.fixedDrawing (9,3) ps)
    (Cell.add (baseline n) ((point.1:Int),(point.2:Int))) (by
      intro offset offsetMember
      apply KeyedPeriodicComplement.ShiftedGadgetReadout.reflected_clause_sound hn period holes admissible
        FixedNormalizedOrientationSeed.fixedDrawing (9,3) carrier ps tiling seed
        FixedNormalizedOrientationSeed.fixedDrawing_wellFormed
        FixedNormalizedOrientationSeed.fixedDrawing_verticesSeparated
      intro location locationMember
      have assoc : Cell.add (Cell.add (baseline n) ((point.1:Int),(point.2:Int))) offset =
          Cell.add (baseline n) (Cell.add ((point.1:Int),(point.2:Int)) offset) := by
        ext <;> simp [Cell.add,add_assoc]
      rw [assoc]
      exact NormalizedOrientation.AsCNF.quarter_lift_deep _ n windowRadius point offsetMember locationMember)
    clause member
  simpa only [wangAssignment,PeriodicClause.Holds,PeriodicLiteral.Holds,Cell.add,add_assoc] using forced

open Lean Elab Command in
run_cmd do
  let axioms ← Lean.collectAxioms ``quarter_satisfies
  let extra := axioms.filter fun ax =>
    ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
  unless extra.isEmpty do throwError "quarter_satisfies depends on unexpected axioms: {extra}"

end LeanTrominoes.FixedPolyominoSeed
