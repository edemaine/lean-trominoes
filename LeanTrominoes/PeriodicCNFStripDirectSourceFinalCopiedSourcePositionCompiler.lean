/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCompactAtomIdentityCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCopiedOccurrenceBlockCompiler
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderCopiedSourcePositionSemantics

/-! # Direct compact-source positions of copied final occurrences -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicCNF.FormulaShapeDirectionOrdering
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCopiedSourcePositionStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Compact pre-Figure9 presentation position queried by each final copied
occurrence.  Values at parent-local occurrences are harmless. -/
def directSourceFinalCopiedSourcePositions
    (symbols : List encoding.Γ) : List Nat :=
  HorizontalRoutedRouteHeaderCopiedSourcePosition.positions
    (directRetainedFigureNineCopiedClauseDescriptors decider symbols)

/-- The direct query column has one entry per copied final occurrence. -/
theorem directSourceFinalCopiedSourcePositions_length
    (symbols : List encoding.Γ) :
    (directSourceFinalCopiedSourcePositions decider symbols).length =
      (directSourceFinalCopiedOccurrenceData decider symbols).length := by
  unfold directSourceFinalCopiedSourcePositions
    directSourceFinalCopiedOccurrenceData
  exact HorizontalRoutedRouteHeaderCopiedSourcePosition.positions_length _

theorem totalSourceWordCount_eq_aritySum (source : List Token) :
    HorizontalRoutedRouteHeaderCopiedSourcePosition.totalSourceWordCount
        source =
      (source.map retainedFinalCopiedDescriptorArity).sum := by
  induction source with
  | nil => rfl
  | cons token source induction =>
      cases token with
      | «variable» =>
          simpa [HorizontalRoutedRouteHeaderCopiedSourcePosition.totalSourceWordCount,
            retainedFinalCopiedDescriptorArity] using induction
      | clause profile =>
          simp [HorizontalRoutedRouteHeaderCopiedSourcePosition.totalSourceWordCount,
            HorizontalRoutedRouteHeaderCopiedSourcePosition.sourceWordCount,
            HorizontalRoutedRouteHeaderCopiedScopedAtomWords.sourceWordCount,
            retainedFinalCopiedDescriptorArity, induction]

/-- The direct compact identity column has exactly the total presentation
arity consumed by its copied descriptor stream. -/
theorem
    directSourceFinalCompactOccurrenceAtomIdentityIndices_length_eq_total
    (symbols : List encoding.Γ) :
    (directSourceFinalCompactOccurrenceAtomIdentityIndices
        decider symbols).length =
      HorizontalRoutedRouteHeaderCopiedSourcePosition.totalSourceWordCount
        (directRetainedFigureNineCopiedClauseDescriptors decider symbols) := by
  let source :=
    directRetainedFigureNineCopiedClauseDescriptors decider symbols
  calc
    (directSourceFinalCompactOccurrenceAtomIdentityIndices
        decider symbols).length =
        ((directRetainedFigureNineCopiedClauseDescriptors
          decider symbols).map retainedFinalCopiedDescriptorArity).sum :=
      directSourceFinalCompactOccurrenceAtomIdentityIndices_length
        decider symbols
    _ = (source.map retainedFinalCopiedDescriptorArity).sum := rfl
    _ = HorizontalRoutedRouteHeaderCopiedSourcePosition.totalSourceWordCount
          source := (totalSourceWordCount_eq_aritySum source).symm

/-- Every direct source query is in range of the compiled compact identity
column that it will index. -/
theorem directSourceFinalCopiedSourcePositions_forall_lt
    (symbols : List encoding.Γ) :
    (directSourceFinalCopiedSourcePositions decider symbols).Forall
      fun position => position <
        (directSourceFinalCompactOccurrenceAtomIdentityIndices
          decider symbols).length := by
  unfold directSourceFinalCopiedSourcePositions
  generalize sourceEq :
      directRetainedFigureNineCopiedClauseDescriptors decider symbols = source
  have bounded :
      (HorizontalRoutedRouteHeaderCopiedSourcePosition.positions source).Forall
        fun position => position <
          HorizontalRoutedRouteHeaderCopiedSourcePosition.totalSourceWordCount
            source :=
    HorizontalRoutedRouteHeaderCopiedSourcePosition.positions_forall_lt
      source
  have identityLength :
      (directSourceFinalCompactOccurrenceAtomIdentityIndices
        decider symbols).length =
        (source.map retainedFinalCopiedDescriptorArity).sum := by
    rw [← sourceEq]
    exact
      directSourceFinalCompactOccurrenceAtomIdentityIndices_length
        decider symbols
  rw [totalSourceWordCount_eq_aritySum] at bounded
  rw [← identityLength] at bounded
  exact bounded

/-- Direct copied compact-source positions are polynomial-time computable as
unary fields. -/
noncomputable def
    directSourceFinalCopiedSourcePositionsComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalCopiedSourcePositions decider) := by
  unfold directSourceFinalCopiedSourcePositions
  exact TM2CompositionMachine.computableInPolyTime
    (directRetainedFigureNineCopiedClauseDescriptorsComputableInPolyTime
      decider)
    HorizontalRoutedRouteHeaderCopiedSourcePosition.positionsComputableInPolyTime

end LeanTrominoes.PeriodicCNFStripReduction

end
