/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataDescriptors
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarDirectionDescriptorData
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataDirectionDescriptorData

/-! # Exact direct retained descriptors from finite metadata -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedPlanarMetadataDirectionSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directRetainedPlanarMetadataDirectionSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  Classical.decEq _

/-- The direct metadata stream is exactly the canonical pre-split retained
planar direction stream. -/
theorem directRetainedPlanarDirectionDescriptors_eq_metadata
    (symbols : List encoding.Γ) :
    directRetainedPlanarDirectionDescriptors decider symbols =
      directRetainedPlanarMetadataDirectionDescriptors decider symbols := by
  unfold directRetainedPlanarDirectionDescriptors
    directRetainedPlanarMetadataDirectionDescriptors
  exact FormulaShapeRetainedPlanarMetadataDirection.descriptors_eq _

end PeriodicCNFStripReduction
end LeanTrominoes
