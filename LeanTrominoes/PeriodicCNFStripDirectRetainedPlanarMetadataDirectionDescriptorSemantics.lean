/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataDescriptors
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarDirectionDescriptorData
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataDirectionDescriptorData

/-! # Exact direct retained descriptors from finite metadata -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


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
