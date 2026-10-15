/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Complexity.FiniteAlphabetKeyedValueLookupCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Occurrence.PeriodicCNFStripDirectSourceFinalOccurrenceCandidateKeyCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Occurrence.PeriodicCNFStripDirectSourceFinalOccurrenceSlotCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Unique.PeriodicCNFStripDirectSourceFinalUniqueFanQueryKeyCompiler
import LeanTrominoes.Computation.TM2.TM2EmptyAlphabetListInputCompiler

/-! # Final occurrence slots in variable-major stable-rank order -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicOneInThreeToThreeDM

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


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
