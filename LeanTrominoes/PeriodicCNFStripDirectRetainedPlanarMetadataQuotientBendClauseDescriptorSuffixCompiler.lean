/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataBaseBendClauseDescriptorCompiler
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataQuotientRoutedClauseDescriptorSuffixCompiler
import LeanTrominoes.TM2NativeListAppendClosure

/-! # Compiling the quotiented bend descriptor suffix -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance quotientBendSuffixStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

noncomputable def
    directRetainedPlanarMetadataQuotientBendClauseDescriptorSuffixComputableInPolyTime :
    DirectRetainedPlanarMetadataQuotientBendClauseDescriptorSuffixCompiler
      decider := by
  change @TM2ComputableInPolyTime
    (List encoding.Γ)
    (List FormulaShapeDirectionOrdering.Token)
    encoding.Γ FormulaShapeDirectionOrdering.Token id id
    (fun symbols =>
      directRetainedPlanarMetadataBaseBendClauseDescriptors
          decider symbols ++
        directRetainedPlanarMetadataQuotientRoutedClauseDescriptorSuffix
          decider symbols)
  exact TM2ListAppend.nativeComputableInPolyTime
    (directRetainedPlanarMetadataBaseBendClauseDescriptorsComputableInPolyTime
      decider)
    (directRetainedPlanarMetadataQuotientRoutedClauseDescriptorSuffixComputableInPolyTime
      decider)

end LeanTrominoes.PeriodicCNFStripReduction

end
