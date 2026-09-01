/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteAlphabetKeyedValueLookupCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceCandidateKeyCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceSlotCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalUniqueFanQueryKeyCompiler
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler

/-! # Final occurrence slots in variable-major stable-rank order -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicOneInThreeToThreeDM

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalGroupedOccurrenceSlotStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Every active final occurrence slot exactly once, in stable
identity-major and occurrence-rank-minor order. -/
def directSourceFinalGroupedOccurrenceSlots
    (symbols : List encoding.Γ) : List OccurrenceSlot :=
  FiniteAlphabetKeyedValueLookup.values
    (directSourceFinalUniqueFanQueryKeys decider symbols)
    (directSourceFinalOccurrenceCandidateKeys decider symbols)
    (directSourceFinalOccurrenceSlots decider symbols)

/-- Finite keyed selection compiles the variable-major occurrence-slot
column in polynomial time. -/
noncomputable def
    directSourceFinalGroupedOccurrenceSlotsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalGroupedOccurrenceSlots decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalGroupedOccurrenceSlots
    exact FiniteAlphabetKeyedValueLookup.valuesComputableInPolyTime
      id
      (directSourceFinalUniqueFanQueryKeys decider)
      (directSourceFinalOccurrenceCandidateKeys decider)
      (directSourceFinalOccurrenceSlots decider)
      (fun symbols => by
        rw [directSourceFinalOccurrenceCandidateKeys_length,
          directSourceFinalOccurrenceSlots_length])
      (directSourceFinalUniqueFanQueryKeysComputableInPolyTime decider)
      (directSourceFinalOccurrenceCandidateKeysComputableInPolyTime decider)
      (directSourceFinalOccurrenceSlotsComputableInPolyTime decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime id _

end LeanTrominoes.PeriodicCNFStripReduction

end
