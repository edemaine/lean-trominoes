/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarThreeOccurrenceEndpoint
import LeanTrominoes.PeriodicWangPlanarThreeDMReduction

/-! # Plane planar 3SAT-3 completeness with supplied periodic drawings -/
noncomputable section
namespace LeanTrominoes.PeriodicPlanarSAT.ThreeOccurrenceGeometry.WangReduction
open PeriodicWangPlanarThreeDMReduction
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 2000000
abbrev TargetVariable := Target Variable

def input (tiles : LeanWang.TileSet) : Input TargetVariable :=
  ThreeOccurrenceGeometry.input (sourceFormula tiles)

theorem input_computable : Computable input :=
  input_primrec.to_comp.comp sourceFormula_computable

theorem correct (tiles : LeanWang.TileSet) :
    LeanWang.TilesPlane tiles ↔ Orbit.ThreeOccurrenceProblem (input tiles) :=
  (sourceFormula_correct tiles).trans
    (input_correct (sourceFormula tiles) (sourceFormula_isLocal tiles)
      (sourceFormula_widthAtMostThree tiles) (sourceFormula_occurrencesAtMostThree_canonicalBEq tiles)
      (sourceFormula_clausesNonempty tiles)).symm

/-- The supplied drawings have injective periodic vertex placements and
continuous route separation. Locality and polynomial grid-size restrictions
are not included in this endpoint. -/
theorem coREComplete : LeanWang.CoREComplete (Orbit.ThreeOccurrenceProblem (V := TargetVariable)) := by
  refine ⟨Orbit.threeOccurrenceProblem_coRE,?_⟩
  intro A _ source hs
  obtain ⟨f,hf,hcorrect⟩ := LeanWang.domino_problem_coRE_hard source hs
  exact ⟨input ∘ f,input_computable.comp hf,fun a => (hcorrect a).trans (correct (f a))⟩
end LeanTrominoes.PeriodicPlanarSAT.ThreeOccurrenceGeometry.WangReduction
