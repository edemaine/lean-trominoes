/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNormalizedRoutedVariablePairCompiledCompiler
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataNormalizedRoutedVariableDescriptorData
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorPairFieldTagCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Compiling direct normalized routed-variable descriptors -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directNormalizedRoutedVariableCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Compile direct-source descriptor pairs and apply the normalized affine
routed-variable scan. -/
noncomputable def
    directRetainedPlanarMetadataNormalizedRoutedVariableClauseDescriptorsComputableInPolyTime :
    DirectRetainedPlanarMetadataNormalizedRoutedVariableClauseDescriptorCompiler
      decider := by
  let fields :=
    directSourceRouteDescriptorPairFieldTagsComputableInPolyTime decider
  let descriptors :=
    FormulaShapeRetainedPlanarMetadataDirection.compiledNormalizedRoutedVariablePairDescriptorStreamComputableInPolyTime
  let complete :=
    TM2CompositionMachine.computableInPolyTime fields descriptors
  change @TM2ComputableInPolyTime
    (List encoding.Γ)
    (List FormulaShapeDirectionOrdering.Token)
    encoding.Γ FormulaShapeDirectionOrdering.Token id id
    (fun symbols =>
      FormulaShapeRetainedPlanarMetadataDirection.compiledNormalizedRoutedVariablePairDescriptorStream
        (directSourceRouteDescriptorPairFieldTags decider symbols))
  exact complete

end LeanTrominoes.PeriodicCNFStripReduction

end
