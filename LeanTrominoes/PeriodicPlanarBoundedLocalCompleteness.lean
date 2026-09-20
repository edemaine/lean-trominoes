/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarLocalThreeOccurrenceCompleteness
import LeanTrominoes.PeriodicPlanarLocalExactOneCompleteness
import LeanTrominoes.PeriodicPlanarExactOneIntrinsicGridSize
import LeanTrominoes.PeriodicPlanarBoundedLocalCoRE

/-! # Local planar completeness with linearly bounded supplied grids

The bound is intrinsic: it uses the output formula's own clause-plus-literal
count. Both ordinary and exact-one languages remain co-r.e. complete, with
or without the additional three-occurrence restriction.
-/
noncomputable section
namespace LeanTrominoes.PeriodicPlanarSAT
open PeriodicWangPlanarThreeDMReduction
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 2000000
namespace ThreeOccurrenceGeometry.WangReduction

theorem intrinsic_gridBound (tiles : LeanWang.TileSet) : GridBound 8847360 (input tiles) :=
  drawing_gridSize_le_output_size (sourceFormula tiles)
    (sourceFormula_occurrencesAtMostThree_canonicalBEq tiles) (sourceFormula_clausesNonempty tiles)

theorem boundedLocal_correct (tiles : LeanWang.TileSet) :
    LeanWang.TilesPlane tiles ↔ Orbit.BoundedLocalProblem (input tiles) :=
  (localProblem_correct tiles).trans (and_iff_right (intrinsic_gridBound tiles)).symm

theorem boundedLocalThreeOccurrence_correct (tiles : LeanWang.TileSet) :
    LeanWang.TilesPlane tiles ↔ Orbit.BoundedLocalThreeOccurrenceProblem (input tiles) :=
  (local_correct tiles).trans (and_iff_right (intrinsic_gridBound tiles)).symm

theorem boundedLocalCoREComplete :
    LeanWang.CoREComplete (Orbit.BoundedLocalProblem (V := TargetVariable)) := by
  refine ⟨Orbit.boundedLocalProblem_coRE,?_⟩
  intro A _ source hs
  obtain ⟨f,hf,hcorrect⟩ := LeanWang.domino_problem_coRE_hard source hs
  exact ⟨input ∘ f,input_computable.comp hf,fun a => (hcorrect a).trans (boundedLocal_correct (f a))⟩

theorem boundedLocalThreeOccurrenceCoREComplete :
    LeanWang.CoREComplete (Orbit.BoundedLocalThreeOccurrenceProblem (V := TargetVariable)) := by
  refine ⟨Orbit.boundedLocalThreeOccurrenceProblem_coRE,?_⟩
  intro A _ source hs
  obtain ⟨f,hf,hcorrect⟩ := LeanWang.domino_problem_coRE_hard source hs
  exact ⟨input ∘ f,input_computable.comp hf,fun a => (hcorrect a).trans (boundedLocalThreeOccurrence_correct (f a))⟩
end ThreeOccurrenceGeometry.WangReduction
namespace ExactOneEndpoint.WangReduction
local instance boundedCompletenessTargetDecidableEq : DecidableEq TargetVariable :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

theorem intrinsic_gridBound (tiles : LeanWang.TileSet) : GridBound 637009920 (input tiles) :=
  drawing_gridSize_le_output_size (sourceFormula tiles) (sourceFormula_isLocal tiles)
    (sourceFormula_widthAtMostThree tiles) (sourceFormula_occurrencesAtMostThree_canonicalBEq tiles)
    (sourceFormula_clausesNonempty tiles)

theorem boundedLocal_correct (tiles : LeanWang.TileSet) :
    LeanWang.TilesPlane tiles ↔ Unbounded.BoundedLocalExactOneProblem (input tiles) :=
  (local_correct tiles).trans (and_iff_right (intrinsic_gridBound tiles)).symm

theorem boundedLocalThreeOccurrence_correct (tiles : LeanWang.TileSet) :
    LeanWang.TilesPlane tiles ↔ Unbounded.BoundedLocalExactOneThreeOccurrenceProblem (input tiles) :=
  (localThreeOccurrence_correct tiles).trans (and_iff_right (intrinsic_gridBound tiles)).symm

theorem boundedLocalCoREComplete :
    LeanWang.CoREComplete (Unbounded.BoundedLocalExactOneProblem (V := TargetVariable)) := by
  refine ⟨Unbounded.boundedLocalExactOneProblem_coRE,?_⟩
  intro A _ source hs
  obtain ⟨f,hf,hcorrect⟩ := LeanWang.domino_problem_coRE_hard source hs
  exact ⟨input ∘ f,input_computable.comp hf,fun a => (hcorrect a).trans (boundedLocal_correct (f a))⟩

theorem boundedLocalThreeOccurrenceCoREComplete :
    LeanWang.CoREComplete (Unbounded.BoundedLocalExactOneThreeOccurrenceProblem (V := TargetVariable)) := by
  refine ⟨Unbounded.boundedLocalExactOneThreeOccurrenceProblem_coRE,?_⟩
  intro A _ source hs
  obtain ⟨f,hf,hcorrect⟩ := LeanWang.domino_problem_coRE_hard source hs
  exact ⟨input ∘ f,input_computable.comp hf,fun a => (hcorrect a).trans (boundedLocalThreeOccurrence_correct (f a))⟩
end ExactOneEndpoint.WangReduction
end LeanTrominoes.PeriodicPlanarSAT
