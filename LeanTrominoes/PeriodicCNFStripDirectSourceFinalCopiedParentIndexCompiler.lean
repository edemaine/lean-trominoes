/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCopiedOccurrenceBlockCompiler
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderCopiedParentIndexCompiler

/-! # Direct copied-clause parent indices -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCopiedParentIndexStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Zero-based parent copied-clause index of every direct final occurrence. -/
def directSourceFinalCopiedParentIndices
    (symbols : List encoding.Γ) : List Nat :=
  HorizontalRoutedRouteHeaderCopiedParentIndex.parentIndices
    (directRetainedFigureNineCopiedClauseDescriptors decider symbols)

/-- The direct parent-index column has one entry per copied occurrence. -/
theorem directSourceFinalCopiedParentIndices_length
    (symbols : List encoding.Γ) :
    (directSourceFinalCopiedParentIndices decider symbols).length =
      (directSourceFinalCopiedOccurrenceData decider symbols).length := by
  unfold directSourceFinalCopiedParentIndices
    directSourceFinalCopiedOccurrenceData
  exact HorizontalRoutedRouteHeaderCopiedParentIndex.parentIndices_length _

/-- The prefix-sum implementation agrees with the explicit blockwise
parent-index presentation. -/
theorem directSourceFinalCopiedParentIndices_eq_expected
    (symbols : List encoding.Γ) :
    directSourceFinalCopiedParentIndices decider symbols =
      HorizontalRoutedRouteHeaderCopiedParentIndex.expected
        (directRetainedFigureNineCopiedClauseDescriptors decider symbols) := by
  unfold directSourceFinalCopiedParentIndices
  exact HorizontalRoutedRouteHeaderCopiedParentIndex.parentIndices_eq_expected _

/-- Direct copied parent indices are polynomial-time computable as unary
fields. -/
noncomputable def
    directSourceFinalCopiedParentIndicesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalCopiedParentIndices decider) := by
  unfold directSourceFinalCopiedParentIndices
  exact TM2CompositionMachine.computableInPolyTime
    (directRetainedFigureNineCopiedClauseDescriptorsComputableInPolyTime
      decider)
    HorizontalRoutedRouteHeaderCopiedParentIndex.parentIndicesComputableInPolyTime

end LeanTrominoes.PeriodicCNFStripReduction

end
