/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataDescriptorBlocks
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataDirectionDescriptorBlockData

/-! # Exact direct retained metadata descriptor block split -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedMetadataBlocksStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directRetainedMetadataBlocksVariableDecidableEq :
    DecidableEq Variable :=
  Classical.decEq _

/-- The direct metadata stream is exactly its separately streamable clause
and variable phases. -/
theorem directRetainedPlanarMetadataDirectionDescriptors_eq_blocks
    (symbols : List encoding.Γ) :
    directRetainedPlanarMetadataDirectionDescriptors decider symbols =
      directRetainedPlanarMetadataClauseDescriptors decider symbols ++
        directRetainedPlanarMetadataVariableMarkers decider symbols := by
  unfold directRetainedPlanarMetadataDirectionDescriptors
    directRetainedPlanarMetadataClauseDescriptors
    directRetainedPlanarMetadataVariableMarkers
    directSourceFormula
  rw [FormulaShapeRetainedPlanarMetadataDirection.descriptors_eq_blocks]
  apply congrArg₂ List.append
  · rfl
  · exact congrArg
      (fun equality : DecidableEq Variable =>
        @FormulaShapeRetainedPlanarMetadataDirection.variableMarkers
          Variable equality
          (sourceFormula (PolySpaceCompiler.formulaOfSymbols decider symbols)))
      (Subsingleton.elim _ _)

end PeriodicCNFStripReduction
end LeanTrominoes
