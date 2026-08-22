/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataClauseDescriptorFamilyData
import LeanTrominoes.TM2NativeListAppendClosure

/-! # Compiling the routed retained clause-descriptor suffix -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedRoutedSuffixCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

noncomputable def
    directRetainedPlanarMetadataRoutedClauseDescriptorSuffixComputableInPolyTime
    (routedClause :
      DirectRetainedPlanarMetadataRoutedClauseDescriptorCompiler decider)
    (routedVariable :
      DirectRetainedPlanarMetadataRoutedVariableClauseDescriptorCompiler
        decider) :
    DirectRetainedPlanarMetadataRoutedClauseDescriptorSuffixCompiler
      decider := by
  change @TM2ComputableInPolyTime
    (List encoding.Γ) (List FormulaShapeDirectionOrdering.Token)
    encoding.Γ FormulaShapeDirectionOrdering.Token id id
    (fun symbols =>
      directRetainedPlanarMetadataRoutedClauseDescriptors decider symbols ++
        directRetainedPlanarMetadataRoutedVariableClauseDescriptors
          decider symbols)
  exact TM2ListAppend.nativeComputableInPolyTime
    routedClause routedVariable

end LeanTrominoes.PeriodicCNFStripReduction

end
