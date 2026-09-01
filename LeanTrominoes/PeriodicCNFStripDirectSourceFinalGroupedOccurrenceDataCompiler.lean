/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteAlphabetKeyedValueLookupCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFanOccurrenceDataCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalUniqueFanQueryKeyCompiler
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler

/-! # Final occurrence records in variable-major stable-rank order -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalGroupedOccurrenceDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Every active final occurrence record exactly once, in stable
identity-major and occurrence-rank-minor order. -/
def directSourceFinalGroupedOccurrenceData
    (symbols : List encoding.Γ) : List FinalFanOccurrenceData :=
  FiniteAlphabetKeyedValueLookup.values
    (directSourceFinalUniqueFanQueryKeys decider symbols)
    (directSourceFinalOccurrenceCandidateKeys decider symbols)
    (directSourceFinalCompiledOccurrenceData decider symbols)

/-- Finite keyed selection compiles the variable-major occurrence-record
column in polynomial time. -/
noncomputable def
    directSourceFinalGroupedOccurrenceDataComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalGroupedOccurrenceData decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalGroupedOccurrenceData
    exact FiniteAlphabetKeyedValueLookup.valuesComputableInPolyTime
      id
      (directSourceFinalUniqueFanQueryKeys decider)
      (directSourceFinalOccurrenceCandidateKeys decider)
      (directSourceFinalCompiledOccurrenceData decider)
      (fun symbols => by
        rw [directSourceFinalOccurrenceCandidateKeys_length])
      (directSourceFinalUniqueFanQueryKeysComputableInPolyTime decider)
      (directSourceFinalOccurrenceCandidateKeysComputableInPolyTime decider)
      (directSourceFinalCompiledOccurrenceDataComputableInPolyTime decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime id _

end LeanTrominoes.PeriodicCNFStripReduction

end
