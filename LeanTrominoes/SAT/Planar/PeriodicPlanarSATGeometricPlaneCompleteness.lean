/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Planar.PeriodicPlanarSATGeometricCoRE

/-! # Plane SAT completeness with faithful supplied geometric certificates -/
noncomputable section
namespace LeanTrominoes.PeriodicPlanarSAT
open PeriodicWangPlanarThreeDMReduction
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 2000000

namespace ThreeOccurrenceGeometry.WangReduction
 theorem geometry (tiles : LeanWang.TileSet) : StrongGeometry (input tiles).2 :=
  ThreeOccurrenceGeometry.strongGeometry (sourceFormula tiles) (sourceFormula_isLocal tiles)
    (sourceFormula_widthAtMostThree tiles) (sourceFormula_occurrencesAtMostThree_canonicalBEq tiles)
    (sourceFormula_clausesNonempty tiles)

 theorem geometricBoundedLocalCoREComplete :
    LeanWang.CoREComplete (Geometric (Orbit.BoundedLocalProblem (V:=TargetVariable))) := by
  refine ⟨GeometricSearch.geometric_coRE Orbit.boundedLocalProblem_coRE,?_⟩
  intro A _ source hs
  obtain ⟨f,hf,hcorrect⟩ := LeanWang.domino_problem_coRE_hard source hs
  refine ⟨input ∘ f,input_computable.comp hf,fun a => ?_⟩
  exact (hcorrect a).trans ((boundedLocal_correct (f a)).trans (and_iff_left (geometry (f a))).symm)

 theorem geometricBoundedLocalThreeOccurrenceCoREComplete :
    LeanWang.CoREComplete (Geometric (Orbit.BoundedLocalThreeOccurrenceProblem (V:=TargetVariable))) := by
  refine ⟨GeometricSearch.geometric_coRE Orbit.boundedLocalThreeOccurrenceProblem_coRE,?_⟩
  intro A _ source hs
  obtain ⟨f,hf,hcorrect⟩ := LeanWang.domino_problem_coRE_hard source hs
  refine ⟨input ∘ f,input_computable.comp hf,fun a => ?_⟩
  exact (hcorrect a).trans ((boundedLocalThreeOccurrence_correct (f a)).trans (and_iff_left (geometry (f a))).symm)
end ThreeOccurrenceGeometry.WangReduction

namespace ExactOneEndpoint.WangReduction
local instance : DecidableEq TargetVariable := PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq
 theorem geometry (tiles : LeanWang.TileSet) : StrongGeometry (input tiles).2 :=
  ExactOneEndpoint.strongGeometry (sourceFormula tiles) (sourceFormula_isLocal tiles)
    (sourceFormula_widthAtMostThree tiles) (sourceFormula_occurrencesAtMostThree_canonicalBEq tiles)
    (sourceFormula_clausesNonempty tiles)

 theorem geometricBoundedLocalCoREComplete :
    LeanWang.CoREComplete (Geometric (Unbounded.BoundedLocalExactOneProblem (V:=TargetVariable))) := by
  refine ⟨GeometricSearch.geometric_coRE Unbounded.boundedLocalExactOneProblem_coRE,?_⟩
  intro A _ source hs
  obtain ⟨f,hf,hcorrect⟩ := LeanWang.domino_problem_coRE_hard source hs
  refine ⟨input ∘ f,input_computable.comp hf,fun a => ?_⟩
  exact (hcorrect a).trans ((boundedLocal_correct (f a)).trans (and_iff_left (geometry (f a))).symm)

 theorem geometricBoundedLocalThreeOccurrenceCoREComplete :
    LeanWang.CoREComplete (Geometric (Unbounded.BoundedLocalExactOneThreeOccurrenceProblem (V:=TargetVariable))) := by
  refine ⟨GeometricSearch.geometric_coRE Unbounded.boundedLocalExactOneThreeOccurrenceProblem_coRE,?_⟩
  intro A _ source hs
  obtain ⟨f,hf,hcorrect⟩ := LeanWang.domino_problem_coRE_hard source hs
  refine ⟨input ∘ f,input_computable.comp hf,fun a => ?_⟩
  exact (hcorrect a).trans ((boundedLocalThreeOccurrence_correct (f a)).trans (and_iff_left (geometry (f a))).symm)
end ExactOneEndpoint.WangReduction
end LeanTrominoes.PeriodicPlanarSAT
