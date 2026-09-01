/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCopiedSourcePositionCompiler
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler
import LeanTrominoes.UnaryIndexedValueLookupCompiler

/-! # Inherited atom identities of direct copied final occurrences -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCopiedInheritedIdentityStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Source-atom identity selected by every copied occurrence's compact-source
position.  Values at parent-local occurrences are intentionally irrelevant. -/
def directSourceFinalCopiedInheritedAtomIdentityIndices
    (symbols : List encoding.Γ) : List Nat :=
  HorizontalRoutedRouteHeaderCopiedSourcePosition.selectedValues
    (directRetainedFigureNineCopiedClauseDescriptors decider symbols)
    (directSourceFinalCompactOccurrenceAtomIdentityIndices decider symbols)

/-- All inherited source identities for the direct copied prefix are
polynomial-time computable as unary fields. -/
noncomputable def
    directSourceFinalCopiedInheritedAtomIdentityIndicesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalCopiedInheritedAtomIdentityIndices decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ :=
      ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalCopiedInheritedAtomIdentityIndices
      HorizontalRoutedRouteHeaderCopiedSourcePosition.selectedValues
    exact UnaryIndexedValueLookup.valuesComputableInPolyTime
      id
      (directSourceFinalCopiedSourcePositions decider)
      (directSourceFinalCompactOccurrenceAtomIdentityIndices decider)
      (directSourceFinalCopiedSourcePositionsComputableInPolyTime decider)
      (directSourceFinalCompactOccurrenceAtomIdentityIndicesComputableInPolyTime
        decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime
      UnaryFieldEncoderMachine.unaryFields _

end LeanTrominoes.PeriodicCNFStripReduction

end
