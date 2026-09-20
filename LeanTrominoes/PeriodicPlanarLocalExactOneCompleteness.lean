/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarExactOneCompleteness
import LeanTrominoes.PeriodicPlanarExactOneLocality
import LeanTrominoes.PeriodicPlanarExactOneGridSize
import LeanTrominoes.PeriodicPlanarLocalCoRE

/-! # Local planar exact-one SAT and occurrence-three completeness -/
noncomputable section
namespace LeanTrominoes.PeriodicPlanarSAT.ExactOneEndpoint.WangReduction
open PeriodicWangPlanarThreeDMReduction
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 2000000
local instance localCompletenessTargetDecidableEq : DecidableEq TargetVariable := PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

theorem input_isLocal (tiles : LeanWang.TileSet) : (input tiles).1.IsLocal :=
  isLocal (sourceFormula tiles) (sourceFormula_isLocal tiles)
    (sourceFormula_widthAtMostThree tiles) (sourceFormula_occurrencesAtMostThree_canonicalBEq tiles)
    (sourceFormula_clausesNonempty tiles)

theorem local_correct (tiles : LeanWang.TileSet) :
    LeanWang.TilesPlane tiles ↔ Unbounded.LocalExactOneProblem (input tiles) :=
  ⟨fun h => ⟨input_isLocal tiles,(correct tiles).1 h⟩,fun h => (correct tiles).2 h.2⟩

theorem localThreeOccurrence_correct (tiles : LeanWang.TileSet) :
    LeanWang.TilesPlane tiles ↔ Unbounded.LocalExactOneThreeOccurrenceProblem (input tiles) := by
  constructor
  · intro h
    have result := (threeOccurrence_correct tiles).1 h
    refine ⟨input_isLocal tiles,?_,result.2⟩
    exact PeriodicCNF.occurrencesAtMost_congr_beq _ _ _ _ 3 _ result.1
  · intro h
    apply (threeOccurrence_correct tiles).2
    exact ⟨PeriodicCNF.occurrencesAtMost_congr_beq _ _ _ _ 3 _ h.2.1,h.2.2⟩

theorem localCoREComplete :
    LeanWang.CoREComplete (Unbounded.LocalExactOneProblem (V := TargetVariable)) := by
  refine ⟨Unbounded.localExactOneProblem_coRE,?_⟩
  intro A _ source hs
  obtain ⟨f,hf,hcorrect⟩ := LeanWang.domino_problem_coRE_hard source hs
  exact ⟨input ∘ f,input_computable.comp hf,fun a => (hcorrect a).trans (local_correct (f a))⟩

theorem localThreeOccurrenceCoREComplete :
    LeanWang.CoREComplete (Unbounded.LocalExactOneThreeOccurrenceProblem (V := TargetVariable)) := by
  refine ⟨Unbounded.localExactOneThreeOccurrenceProblem_coRE,?_⟩
  intro A _ source hs
  obtain ⟨f,hf,hcorrect⟩ := LeanWang.domino_problem_coRE_hard source hs
  exact ⟨input ∘ f,input_computable.comp hf,fun a => (hcorrect a).trans (localThreeOccurrence_correct (f a))⟩

/-- The exact-one replacement multiplies the ordinary drawing period by 72. -/
theorem input_gridSize_bound (tiles : LeanWang.TileSet) :
    (input tiles).2.gridSize ≤ 53084160 * (2*(sourceFormula tiles).presentationSize+1) :=
  drawing_gridSize_le_presentationSize (sourceFormula tiles)

end LeanTrominoes.PeriodicPlanarSAT.ExactOneEndpoint.WangReduction
