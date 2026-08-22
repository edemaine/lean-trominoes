/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataDecomposedVariableMarkerNamedCounts
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataVariableMarkerNamedCounts

/-! # Correctness of decomposed retained variable markers -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedDecomposedMarkerCorrectStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The independently compiled marker phases concatenate to the exact
canonical retained metadata variable-marker suffix. -/
theorem directRetainedPlanarMetadataDecomposedVariableMarkers_eq
    (symbols : List encoding.Γ) :
    directRetainedPlanarMetadataDecomposedVariableMarkers decider symbols =
      directRetainedPlanarMetadataVariableMarkers decider symbols := by
  rw [directRetainedPlanarMetadataDecomposedVariableMarkers_eq_namedCounts]
  rw [directRetainedPlanarMetadataVariableMarkers_eq_namedCounts]
  rfl

end PeriodicCNFStripReduction
end LeanTrominoes

end
