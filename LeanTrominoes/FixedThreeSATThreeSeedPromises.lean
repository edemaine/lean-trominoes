/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FixedThreeSATThreeSeedCompleteness
import LeanTrominoes.PeriodicThreeSATThreeNonempty

/-! # Nonempty clauses at the fixed finite-prescription source -/
namespace LeanTrominoes.FixedThreeSATThreeSeed
open LeanWang FixedMachineWangSeed

theorem universalPlanePalette_ne_nil : PlaneExtension.universalPlanePalette ≠ [] := by
  let tail := tailTile UniversalTM0Machine.machine
  have tailMember : tail ∈ universalPalette := by
    simp only [universalPalette,fixedTiles,List.mem_append,List.mem_singleton]
    exact Or.inr rfl
  let tile := WangTile.product
    (PointedExtension.positionTile .negative .negative) PointedExtension.zeroTile
  have member : tile ∈ PlaneExtension.universalPlanePalette := by
    apply List.mem_flatMap.mpr
    refine ⟨tail,tailMember,PointedExtension.mem_tiles_iff.mpr ?_⟩
    exact ⟨.negative,.negative,PointedExtension.zeroTile,
      by simp [PointedExtension.regionPayloads],rfl⟩
  intro empty
  rw [empty] at member
  exact List.not_mem_nil member

theorem fixedFormula_clausesNonempty : ∀ clause ∈ fixedFormula.clauses, clause ≠ [] :=
  PeriodicThreeSATThree.formula_clausesNonempty splitFormula
    (PeriodicThreeCNF.formula_clausesNonempty WangPeriodicCNF.fixedFormula
      (WangPeriodicCNF.formula_clausesNonempty_of_tiles_ne_nil _ universalPlanePalette_ne_nil))

end LeanTrominoes.FixedThreeSATThreeSeed
