/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordLastIndexIdentityCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCompactOccurrenceAtomWordCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCopiedClauseDescriptorArity
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCopiedScopedAtomWordData
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler

/-! # Numeric identities of direct compact final-source atoms -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCompactAtomIdentityStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- For each pre-Figure9 final-source occurrence, the last presentation
index carrying the same compact atom word. -/
def directSourceFinalCompactOccurrenceAtomIdentityIndices
    (symbols : List encoding.Γ) : List Nat :=
  DelimitedBinaryWordLastIndexIdentity.identityIndices
    (directSourceFinalCompactOccurrenceAtomWords decider symbols)

/-- The identity column remains aligned with the complete pre-Figure9 atom
word column and hence with copied descriptor arity. -/
theorem directSourceFinalCompactOccurrenceAtomIdentityIndices_length
    (symbols : List encoding.Γ) :
    (directSourceFinalCompactOccurrenceAtomIdentityIndices
      decider symbols).length =
      ((directRetainedFigureNineCopiedClauseDescriptors decider symbols).map
        retainedFinalCopiedDescriptorArity).sum := by
  rw [directSourceFinalCompactOccurrenceAtomIdentityIndices,
    DelimitedBinaryWordLastIndexIdentity.identityIndices_length,
    directSourceFinalCopiedScopedAtomWords_sourceLength]

/-- Direct compact source-atom identities are polynomial-time computable as
unary fields. -/
noncomputable def
    directSourceFinalCompactOccurrenceAtomIdentityIndicesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalCompactOccurrenceAtomIdentityIndices decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ :=
      ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalCompactOccurrenceAtomIdentityIndices
    exact DelimitedBinaryWordLastIndexIdentity.computableInPolyTime
      id (directSourceFinalCompactOccurrenceAtomWords decider)
      (directSourceFinalCompactOccurrenceAtomWordsComputableInPolyTime decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime
      UnaryFieldEncoderMachine.unaryFields _

end LeanTrominoes.PeriodicCNFStripReduction

end
