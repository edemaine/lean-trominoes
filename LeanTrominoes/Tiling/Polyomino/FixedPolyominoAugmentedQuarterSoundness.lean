/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Wang.FixedWangAugmentedSeedDecoder
import LeanTrominoes.Tiling.Polyomino.FixedPolyominoSeedPalette

/-! # Quarter-plane soundness with arbitrary unused-variable prescriptions -/
noncomputable section
namespace LeanTrominoes.FixedPolyominoSeed.AugmentedSoundness
open PlusRefinement Gadget KeyedPeriodicComplement PeriodicCNF.SignedDecoder
attribute [local irreducible] FixedNormalizedOrientationSeed.fixedFormula
attribute [local irreducible] coarsePeriod tilePeriod
attribute [local irreducible] ShiftedGadgetReadout.assignment

def windowRadius : Nat := Classical.choose FixedWangAugmentedSeedDecoder.uniform_window
def baseline (extra : Nat) : Cell :=
  NormalizedOrientation.AsCNF.quarterBaseline tilePeriod (windowRadius+extra)

def assignment (ps : Set (Placement Bool))
    (free : FixedWangAugmentedSeedDecoder.PolarityVariable → Cell → Bool) :
    FixedWangAugmentedSeedDecoder.Variable → Cell → Bool :=
  fun v => match v with
  | .inl v => ShiftedGadgetReadout.assignment drawing (9,3) ps v
  | .inr v => free v

theorem restrict_assignment (ps : Set (Placement Bool))
    (free : FixedWangAugmentedSeedDecoder.PolarityVariable → Cell → Bool) :
    PeriodicCNF.UnusedVariables.restrict (assignment ps free) =
      ShiftedGadgetReadout.assignment drawing (9,3) ps := by
  unfold PeriodicCNF.UnusedVariables.restrict assignment
  rfl

attribute [local irreducible] assignment

def wangAssignment (extra : Nat) (ps : Set (Placement Bool))
    (free : FixedWangAugmentedSeedDecoder.PolarityVariable → Cell → Bool) : LeanWang.WangTile → Cell → Bool :=
  fun tile c => decode FixedWangAugmentedSeedDecoder.read (assignment ps free)
    tile (Cell.add (baseline extra) c)

theorem quarter_satisfies (extra : Nat) (ps : Set (Placement Bool))
    (tiling : IsTiling (pairTiles bumpy largeTile) Set.univ ps)
    (seed : referencePlacement ∈ ps)
    (free : FixedWangAugmentedSeedDecoder.PolarityVariable → Cell → Bool) :
    WangPeriodicCNF.QuarterSatisfies FixedMachineWangSeed.PlaneExtension.universalPlanePalette
      (wangAssignment extra ps free) := by
  intro point clause member
  have localRule := Classical.choose_spec FixedWangAugmentedSeedDecoder.uniform_window
  have forced := localRule (assignment ps free)
    (Cell.add (baseline extra) ((point.1:Int),(point.2:Int))) (by
      intro offset offsetMember target targetMember
      unfold FixedWangAugmentedSeedDecoder.formula PeriodicCNF.UnusedVariables.formula at targetMember
      obtain ⟨base,baseMember,rfl⟩ := List.mem_map.mp targetMember
      apply (PeriodicCNF.UnusedVariables.clause_holds _ _ _).2
      rw [restrict_assignment]
      apply ShiftedGadgetReadout.reflected_clause_sound tilePeriod_large tilePeriod_divisible
        fixedHoles fixedHoles_admissible drawing (9,3) fixedHoles_carrier ps tiling seed
        FixedNormalizedOrientationSeed.fixedDrawing_wellFormed
        FixedNormalizedOrientationSeed.fixedDrawing_verticesSeparated
      · intro location locationMember
        have assoc : Cell.add (Cell.add (baseline extra) ((point.1:Int),(point.2:Int))) offset =
            Cell.add (baseline extra) (Cell.add ((point.1:Int),(point.2:Int)) offset) := by
          ext <;> simp [Cell.add,add_assoc]
        rw [assoc]
        exact NormalizedOrientation.AsCNF.quarter_lift_deep _ tilePeriod (windowRadius+extra) point
          (boxCellList_mono (Nat.le_add_right _ _) offset offsetMember) locationMember
      · unfold FixedNormalizedOrientationSeed.fixedFormula at baseMember
        exact baseMember)
    clause member
  simpa only [wangAssignment,PeriodicClause.Holds,PeriodicLiteral.Holds,Cell.add,add_assoc] using forced

end LeanTrominoes.FixedPolyominoSeed.AugmentedSoundness
