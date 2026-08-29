/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceRoleSlotCodeCompiler
import LeanTrominoes.RetainedAngularFanFinalOccurrenceRoleSlotDecoderCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Compiler for final occurrence-role/slot pairs -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalRoleSlotPairStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Decode every aligned role/slot code to its finite occurrence role and
bounded terminal slot. -/
def directSourceFinalOccurrenceRoleSlotPairs
    (symbols : List encoding.Γ) :
    List FinalOccurrenceRoleSlotDecoder.Pair :=
  FinalOccurrenceRoleSlotDecoder.pairs
    (directSourceFinalOccurrenceRoleSlotCodes decider symbols)

/-- The aligned arithmetic code stream followed by the generic finite
decoder compiles the complete final occurrence-role/slot stream. -/
noncomputable def
    directSourceFinalOccurrenceRoleSlotPairsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ)
      (List FinalOccurrenceRoleSlotDecoder.Pair)
      encoding.Γ FinalOccurrenceRoleSlotDecoder.Pair
      id id
      (directSourceFinalOccurrenceRoleSlotPairs decider) := by
  unfold directSourceFinalOccurrenceRoleSlotPairs
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalOccurrenceRoleSlotCodesComputableInPolyTime decider)
    FinalOccurrenceRoleSlotDecoder.computableInPolyTime

end LeanTrominoes.PeriodicCNFStripReduction

end
