/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarThreeOccurrenceCompleteness
import LeanTrominoes.PeriodicPlanarThreeOccurrenceLocality
import LeanTrominoes.PeriodicPlanarThreeOccurrenceGridSize
import LeanTrominoes.PeriodicPlanarLocalCoRE

/-! # Local planar 3SAT and 3SAT-3 completeness -/
noncomputable section
namespace LeanTrominoes.PeriodicPlanarSAT.ThreeOccurrenceGeometry.WangReduction
open PeriodicWangPlanarThreeDMReduction
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 2000000

theorem input_isLocal (tiles : LeanWang.TileSet) : (input tiles).1.IsLocal :=
  isLocal (sourceFormula tiles) (sourceFormula_isLocal tiles)
    (sourceFormula_widthAtMostThree tiles) (sourceFormula_occurrencesAtMostThree_canonicalBEq tiles)

theorem local_correct (tiles : LeanWang.TileSet) :
    LeanWang.TilesPlane tiles ↔ Orbit.LocalThreeOccurrenceProblem (input tiles) :=
  ⟨fun h => ⟨input_isLocal tiles,(correct tiles).1 h⟩,fun h => (correct tiles).2 h.2⟩

theorem localThreeOccurrenceCoREComplete :
    LeanWang.CoREComplete (Orbit.LocalThreeOccurrenceProblem (V := TargetVariable)) := by
  refine ⟨Orbit.localThreeOccurrenceProblem_coRE,?_⟩
  intro A _ source hs
  obtain ⟨f,hf,hcorrect⟩ := LeanWang.domino_problem_coRE_hard source hs
  exact ⟨input ∘ f,input_computable.comp hf,fun a => (hcorrect a).trans (local_correct (f a))⟩

theorem localProblem_correct (tiles : LeanWang.TileSet) :
    LeanWang.TilesPlane tiles ↔ Orbit.LocalProblem (input tiles) := by
  constructor
  · intro h
    have result := (local_correct tiles).1 h
    exact ⟨result.1,result.2.2⟩
  · intro h
    apply (sourceFormula_correct tiles).2
    exact (PeriodicOrthocrossing.retainedFigureNineClearancePositionedFormula_satisfiable_iff
      (sourceFormula tiles) (sourceFormula_isLocal tiles) (sourceFormula_widthAtMostThree tiles)
      (sourceFormula_occurrencesAtMostThree_canonicalBEq tiles)).1 h.2.2.2

theorem localCoREComplete : LeanWang.CoREComplete (Orbit.LocalProblem (V := TargetVariable)) := by
  refine ⟨Orbit.localProblem_coRE,?_⟩
  intro A _ source hs
  obtain ⟨f,hf,hcorrect⟩ := LeanWang.domino_problem_coRE_hard source hs
  exact ⟨input ∘ f,input_computable.comp hf,fun a => (hcorrect a).trans (localProblem_correct (f a))⟩

/-- The completeness reduction uses a grid linear in its intermediate local CNF source size. -/
theorem input_gridSize_bound (tiles : LeanWang.TileSet) :
    (input tiles).2.gridSize ≤ 737280 * (2*(sourceFormula tiles).presentationSize+1) :=
  drawing_period_le_presentationSize (sourceFormula tiles)

end LeanTrominoes.PeriodicPlanarSAT.ThreeOccurrenceGeometry.WangReduction
