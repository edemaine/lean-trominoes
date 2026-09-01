/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalUniqueFanQueryKeyCompiler
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler
import LeanTrominoes.UnaryFieldRangeCompiler
import LeanTrominoes.UnaryKeyedValueLookupCompiler

/-! # Final occurrence indices in variable-major stable-rank order -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalGroupedOccurrenceIndexStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Clause-major zero-based positions aligned with occurrence candidate
keys. -/
def directSourceFinalOccurrenceCandidateIndices
    (symbols : List encoding.Γ) : List Nat :=
  UnaryFieldRange.values
    (directSourceFinalOccurrenceCandidateKeys decider symbols)

/-- Clause-major positions selected in variable-major, stable-rank order. -/
def directSourceFinalGroupedOccurrenceIndices
    (symbols : List encoding.Γ) : List Nat :=
  UnaryKeyedValueLookup.values
    (directSourceFinalUniqueFanQueryKeys decider symbols)
    (directSourceFinalOccurrenceCandidateKeys decider symbols)
    (directSourceFinalOccurrenceCandidateIndices decider symbols)

noncomputable def
    directSourceFinalOccurrenceCandidateIndicesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalOccurrenceCandidateIndices decider) := by
  unfold directSourceFinalOccurrenceCandidateIndices
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalOccurrenceCandidateKeysComputableInPolyTime decider)
    UnaryFieldRange.computableInPolyTime

/-- Keyed lookup compiles the clause-major positions in their required
variable-major order. -/
noncomputable def
    directSourceFinalGroupedOccurrenceIndicesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalGroupedOccurrenceIndices decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalGroupedOccurrenceIndices
    exact UnaryKeyedValueLookup.valuesComputableInPolyTime
      id
      (directSourceFinalUniqueFanQueryKeys decider)
      (directSourceFinalOccurrenceCandidateKeys decider)
      (directSourceFinalOccurrenceCandidateIndices decider)
      (fun symbols => by
        simp [directSourceFinalOccurrenceCandidateIndices,
          UnaryFieldRange.values])
      (directSourceFinalUniqueFanQueryKeysComputableInPolyTime decider)
      (directSourceFinalOccurrenceCandidateKeysComputableInPolyTime decider)
      (directSourceFinalOccurrenceCandidateIndicesComputableInPolyTime
        decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime
      UnaryFieldEncoderMachine.unaryFields _

end LeanTrominoes.PeriodicCNFStripReduction

end
