/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedFinalCopiedClauseDescriptorCompiler
import LeanTrominoes.PeriodicCNFStripDirectRetainedFiniteSourceVariableMarkerCompiler
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderCopiedLocalAtomCodeCompiler
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler
import LeanTrominoes.TM2ListAppendClosure

/-! # Complete direct final parent-clause descriptors -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalClauseDescriptorStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The constant nine-clause implication-cycle descriptor block emitted by
each retained-variable marker. -/
def directSourceFinalCycleClauseDescriptorBlock :
    FormulaShapeDirectionOrdering.Token →
      List FormulaShapeDirectionOrdering.Token :=
  FormulaShapeFixedEightDirection.cycleClauseBlock

/-- All implication-cycle parent descriptors, in retained-variable order. -/
def directSourceFinalCycleClauseDescriptors
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  (directRetainedFigureNineFiniteSourceVariableMarkers
    decider symbols).flatMap directSourceFinalCycleClauseDescriptorBlock

/-- The implication-cycle parent descriptor suffix is polynomial-time
computable by a constant finite block expansion. -/
noncomputable def
    directSourceFinalCycleClauseDescriptorsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalCycleClauseDescriptors decider) := by
  unfold directSourceFinalCycleClauseDescriptors
  exact TM2CompositionMachine.computableInPolyTime
    (directRetainedFigureNineFiniteSourceVariableMarkersComputableInPolyTime
      decider)
    (FiniteBlockTransducer.computableInPolyTime
      directSourceFinalCycleClauseDescriptorBlock)

/-- Complete parent-clause descriptor order: copied source clauses, then all
implication-cycle clauses. -/
def directSourceFinalClauseDescriptors
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  directRetainedFigureNineCopiedClauseDescriptors decider symbols ++
    directSourceFinalCycleClauseDescriptors decider symbols

/-- The complete parent descriptor stream is polynomial-time computable. -/
noncomputable def directSourceFinalClauseDescriptorsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalClauseDescriptors decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ :=
      ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalClauseDescriptors
    exact TM2ListAppend.computableInPolyTime
      (directRetainedFigureNineCopiedClauseDescriptorsComputableInPolyTime
        decider)
      (directSourceFinalCycleClauseDescriptorsComputableInPolyTime decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime id _

/-- Parent-indexed local atom codes over the combined descriptor stream.
Indexing copied and cycle clauses together makes every parent-local namespace
globally disjoint without a later offset. -/
def directSourceFinalLocalAtomCodes
    (symbols : List encoding.Γ) : List Nat :=
  HorizontalRoutedRouteHeaderCopiedLocalAtomCode.codes
    (directSourceFinalClauseDescriptors decider symbols)

theorem directSourceFinalLocalAtomCodes_length
    (symbols : List encoding.Γ) :
    (directSourceFinalLocalAtomCodes decider symbols).length =
      (HorizontalRoutedRouteHeaderOccurrenceBlock.output
        (directSourceFinalClauseDescriptors decider symbols)).length := by
  exact HorizontalRoutedRouteHeaderCopiedLocalAtomCode.codes_length _

/-- Complete globally parent-indexed local atom codes are polynomial-time
computable as unary fields. -/
noncomputable def directSourceFinalLocalAtomCodesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalLocalAtomCodes decider) := by
  unfold directSourceFinalLocalAtomCodes
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalClauseDescriptorsComputableInPolyTime decider)
    HorizontalRoutedRouteHeaderCopiedLocalAtomCode.codesComputableInPolyTime

end LeanTrominoes.PeriodicCNFStripReduction

end
