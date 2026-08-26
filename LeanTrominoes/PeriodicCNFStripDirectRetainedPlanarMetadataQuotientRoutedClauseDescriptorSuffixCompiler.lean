/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataBaseRoutedClauseDescriptorCompiler
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataNormalizedRoutedVariableDescriptorCompiler
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataQuotientClauseDescriptorAssemblyData
import LeanTrominoes.TM2NativeListAppendClosure

/-! # Compiling the quotiented routed descriptor suffix -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance quotientRoutedSuffixStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

noncomputable def
    directRetainedPlanarMetadataQuotientRoutedClauseDescriptorSuffixComputableInPolyTime :
    DirectRetainedPlanarMetadataQuotientRoutedClauseDescriptorSuffixCompiler
      decider := by
  change @TM2ComputableInPolyTime
    (List encoding.Γ)
    (List FormulaShapeDirectionOrdering.Token)
    encoding.Γ FormulaShapeDirectionOrdering.Token id id
    (fun symbols =>
      directRetainedPlanarMetadataBaseRoutedClauseDescriptors
          decider symbols ++
        directRetainedPlanarMetadataNormalizedRoutedVariableClauseDescriptors
          decider symbols)
  exact TM2ListAppend.nativeComputableInPolyTime
    (directRetainedPlanarMetadataBaseRoutedClauseDescriptorsComputableInPolyTime
      decider)
    (directRetainedPlanarMetadataNormalizedRoutedVariableClauseDescriptorsComputableInPolyTime
      decider)

end LeanTrominoes.PeriodicCNFStripReduction

end
