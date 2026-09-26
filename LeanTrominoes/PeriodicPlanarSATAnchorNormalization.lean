/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarSATOneDimensional
import LeanTrominoes.PeriodicCNFAnchorNormalizationLocality
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationSize

/-! # Clause-anchor normalization preserves the ordinary planar promises -/
namespace LeanTrominoes.PeriodicPlanarSAT
variable {V : Type} [Primcodable V] [DecidableEq V]

def anchorInput (input : Input V) : Input V := (input.1.anchorNormalize, input.2)

omit [Primcodable V] [DecidableEq V] in
@[simp] theorem presentationSize_anchorNormalize (formula : PeriodicCNF V) :
    formula.anchorNormalize.presentationSize = formula.presentationSize := by
  simp only [PeriodicCNF.presentationSize, PeriodicCNF.literalCount_anchorNormalize]
  simp [PeriodicCNF.anchorNormalize]

theorem ordinary_anchorInput {input : Input V} (h : Orbit.LocalOneDimensionalProblem input) :
    Orbit.LocalOneDimensionalProblem (anchorInput input) := by
  rcases h with ⟨horizontal, grid, locality, ⟨width, compatible⟩, planar, satisfiable⟩
  refine ⟨PeriodicCNF.anchorNormalize_isOneDimensional horizontal, ?_,
    PeriodicCNF.anchorNormalize_local locality, ⟨?_, ?_⟩, planar, ?_⟩
  · simpa only [GridBound, anchorInput, presentationSize_anchorNormalize] using grid
  · exact PeriodicCNF.anchorNormalize_widthAtMost _ _ width
  · simpa only [anchorInput, PeriodicCNF.incidenceGraph_anchorNormalize] using compatible
  · exact (PeriodicCNF.anchorNormalize_satisfiable_iff input.1).2 satisfiable

theorem ordinaryThree_anchorInput {input : Input V}
    (h : Orbit.LocalOneDimensionalThreeOccurrenceProblem input) :
    Orbit.LocalOneDimensionalThreeOccurrenceProblem (anchorInput input) := by
  rcases h with ⟨horizontal, grid, locality, occurrences, problem⟩
  have ordinary := ordinary_anchorInput (input := input) ⟨horizontal, grid, locality, problem⟩
  exact ⟨ordinary.1, ordinary.2.1, ordinary.2.2.1,
    input.1.anchorNormalize_occurrencesAtMost 3 occurrences, ordinary.2.2.2⟩

end LeanTrominoes.PeriodicPlanarSAT
