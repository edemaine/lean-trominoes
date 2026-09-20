/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarExactOneEndpoint
import LeanTrominoes.PeriodicWangPlanarThreeDMReduction

/-! # Plane planar exact-one SAT completeness with supplied drawings -/
noncomputable section
namespace LeanTrominoes.PeriodicPlanarSAT.ExactOneEndpoint.WangReduction
open PeriodicWangPlanarThreeDMReduction
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 2000000
abbrev TargetVariable := Target Variable
local instance : DecidableEq TargetVariable :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

def input (tiles : LeanWang.TileSet) : Input TargetVariable :=
  ExactOneEndpoint.input (sourceFormula tiles)

theorem input_computable : Computable input := input_primrec.to_comp.comp sourceFormula_computable

theorem correct (tiles : LeanWang.TileSet) :
    LeanWang.TilesPlane tiles ↔ Unbounded.ExactOneProblem (input tiles) :=
  (sourceFormula_correct tiles).trans
    (problem_correct (sourceFormula tiles) (sourceFormula_isLocal tiles)
      (sourceFormula_widthAtMostThree tiles) (sourceFormula_occurrencesAtMostThree_canonicalBEq tiles)
      (sourceFormula_clausesNonempty tiles)).symm

theorem threeOccurrence_correct (tiles : LeanWang.TileSet) :
    LeanWang.TilesPlane tiles ↔ Unbounded.ExactOneThreeOccurrenceProblem (input tiles) :=
  (sourceFormula_correct tiles).trans
    (threeOccurrenceProblem_correct (sourceFormula tiles) (sourceFormula_isLocal tiles)
      (sourceFormula_widthAtMostThree tiles) (sourceFormula_occurrencesAtMostThree_canonicalBEq tiles)
      (sourceFormula_clausesNonempty tiles)).symm

theorem coREComplete : LeanWang.CoREComplete (Unbounded.ExactOneProblem (V := TargetVariable)) := by
  refine ⟨Unbounded.exactOneProblem_coRE,?_⟩
  intro A _ source hs
  obtain ⟨f,hf,hcorrect⟩ := LeanWang.domino_problem_coRE_hard source hs
  exact ⟨input ∘ f,input_computable.comp hf,fun a => (hcorrect a).trans (correct (f a))⟩

theorem threeOccurrenceCoREComplete :
    LeanWang.CoREComplete (Unbounded.ExactOneThreeOccurrenceProblem (V := TargetVariable)) := by
  refine ⟨Unbounded.exactOneThreeOccurrenceProblem_coRE,?_⟩
  intro A _ source hs
  obtain ⟨f,hf,hcorrect⟩ := LeanWang.domino_problem_coRE_hard source hs
  exact ⟨input ∘ f,input_computable.comp hf,fun a => (hcorrect a).trans (threeOccurrence_correct (f a))⟩
end LeanTrominoes.PeriodicPlanarSAT.ExactOneEndpoint.WangReduction
