/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNormalizedRoutedVariablePairCompiledData
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorPairFieldTagData

/-! # Direct normalized routed-variable descriptors -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directNormalizedRoutedVariableDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Evaluate the normalized routed-variable pair scan on the direct source's
exact tagged descriptor square. -/
def directRetainedPlanarMetadataNormalizedRoutedVariableClauseDescriptors
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  FormulaShapeRetainedPlanarMetadataDirection.compiledNormalizedRoutedVariablePairDescriptorStream
    (directSourceRouteDescriptorPairFieldTags decider symbols)

abbrev
    DirectRetainedPlanarMetadataNormalizedRoutedVariableClauseDescriptorCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ)
    (List FormulaShapeDirectionOrdering.Token)
    encoding.Γ FormulaShapeDirectionOrdering.Token id id
    (directRetainedPlanarMetadataNormalizedRoutedVariableClauseDescriptors
      decider)

end LeanTrominoes.PeriodicCNFStripReduction

end
