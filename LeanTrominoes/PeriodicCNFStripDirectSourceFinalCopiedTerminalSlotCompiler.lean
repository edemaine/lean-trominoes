/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCopiedSourcePositionCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceRoleSlotFieldCompilers
import LeanTrominoes.RetainedAngularOccurrenceGlobalStableRankLength
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler
import LeanTrominoes.UnaryIndexedValueLookupCompiler

/-! # Terminal slots of direct copied final occurrences -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCopiedTerminalSlotStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCopiedTerminalSlotVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The pre-Figure9 terminal-slot column has exactly the total presentation
arity consumed by the copied descriptor stream. -/
theorem directSourceFinalTerminalSlotValues_length_eq_total
    (symbols : List encoding.Γ) :
    (directSourceFinalTerminalSlotValues decider symbols).length =
      HorizontalRoutedRouteHeaderCopiedSourcePosition.totalSourceWordCount
        (directRetainedFigureNineCopiedClauseDescriptors decider symbols) := by
  rw [totalSourceWordCount_eq_aritySum]
  rw [directSourceFinalCopiedClauseDescriptorAritySum_eq]
  unfold directSourceFinalTerminalSlotValues FiniteUnaryFieldMap.values
    BoundedRetainedTerminalSlots.slots
  simp only [List.length_map]
  rw [retainedOccurrenceGlobalStableTerminalRanks_length]
  unfold retainedFinalCoordinatedScaledSource
  rw [PositionedPeriodicCNF.erase_scale]

/-- Terminal port slot selected by every copied occurrence's compact-source
position.  Values at parent-local occurrences are intentionally irrelevant. -/
def directSourceFinalCopiedTerminalSlotValues
    (symbols : List encoding.Γ) : List Nat :=
  HorizontalRoutedRouteHeaderCopiedSourcePosition.selectedValues
    (directRetainedFigureNineCopiedClauseDescriptors decider symbols)
    (directSourceFinalTerminalSlotValues decider symbols)

/-- All copied terminal slots are polynomial-time computable as unary
fields. -/
noncomputable def
    directSourceFinalCopiedTerminalSlotValuesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalCopiedTerminalSlotValues decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ :=
      ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalCopiedTerminalSlotValues
      HorizontalRoutedRouteHeaderCopiedSourcePosition.selectedValues
    exact UnaryIndexedValueLookup.valuesComputableInPolyTime
      id
      (directSourceFinalCopiedSourcePositions decider)
      (directSourceFinalTerminalSlotValues decider)
      (directSourceFinalCopiedSourcePositionsComputableInPolyTime decider)
      (directSourceFinalTerminalSlotValuesComputableInPolyTime decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime
      UnaryFieldEncoderMachine.unaryFields _

end LeanTrominoes.PeriodicCNFStripReduction

end
