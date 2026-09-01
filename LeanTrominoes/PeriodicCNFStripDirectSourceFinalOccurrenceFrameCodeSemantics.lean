/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.AlignedThreeNatColumns
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceFrameCompiler
import LeanTrominoes.UnaryAlignedAddSemantics

/-! # Code-column semantics for complete direct final occurrence frames -/

noncomputable section

set_option maxHeartbeats 800000

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicOneInThreeToThreeDM

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Declarative pointwise assembly of the three independently compiled finite
frame columns. -/
def directSourceFinalOccurrenceFramesExpected
    (symbols : List encoding.Γ) :
    List DirectFinalOccurrenceFrame.Data :=
  List.zip
      (directSourceFinalVariableFanData decider symbols)
      (List.zip
        (directSourceFinalOccurrenceSlots decider symbols)
        (directSourceFinalClauseFrames decider symbols))
    |>.map fun aligned =>
      { variableFan := aligned.1
        occurrenceSlot := aligned.2.1
        clauseFrame := aligned.2.2 }

/-- The two aligned unary additions produce exactly the mixed-radix code of
each declaratively assembled frame. -/
theorem directSourceFinalOccurrenceFrameCodes_eq_expected_map
    (symbols : List encoding.Γ) :
    directSourceFinalOccurrenceFrameCodes decider symbols =
      (directSourceFinalOccurrenceFramesExpected decider symbols).map
        DirectFinalOccurrenceFrame.codeOfData := by
  unfold directSourceFinalOccurrenceFrameCodes
    directSourceFinalOccurrenceFrameRoleBases
    AlignedUnaryListClosure.added
  have roleLength :
      (directSourceFinalOccurrenceFrameVariableFanBases decider symbols).length =
        (directSourceFinalOccurrenceFrameClauseBases decider symbols).length :=
    (directSourceFinalOccurrenceFrameVariableFanBases_length
      decider symbols).trans
      (directSourceFinalOccurrenceFrameClauseBases_length
        decider symbols).symm
  let roleValid := UnaryAlignedAddMachine.Valid.of_length_eq roleLength
  have completeLength :
      (UnaryAlignedAddMachine.sums
        (directSourceFinalOccurrenceFrameVariableFanBases decider symbols)
        (directSourceFinalOccurrenceFrameClauseBases decider symbols)).length =
        (directSourceFinalOccurrenceFrameSlotValues decider symbols).length := by
    rw [UnaryAlignedAddMachine.sums_length roleValid,
      directSourceFinalOccurrenceFrameVariableFanBases_length,
      directSourceFinalOccurrenceFrameSlotValues_length]
  let completeValid :=
    UnaryAlignedAddMachine.Valid.of_length_eq completeLength
  rw [UnaryAlignedAddMachine.sums_eq_zipWith completeValid,
    UnaryAlignedAddMachine.sums_eq_zipWith roleValid]
  unfold directSourceFinalOccurrenceFrameVariableFanBases
    directSourceFinalOccurrenceFrameClauseBases
    directSourceFinalOccurrenceFrameSlotValues
    FiniteUnaryFieldMap.values
    directSourceFinalOccurrenceFramesExpected
  generalize fanDataEq :
    directSourceFinalVariableFanData decider symbols = fans
  generalize slotsEq :
    directSourceFinalOccurrenceSlots decider symbols = slots
  generalize clausesEq :
    directSourceFinalClauseFrames decider symbols = clauses
  have slotLength : slots.length = fans.length := by
    rw [← slotsEq, ← fanDataEq,
      directSourceFinalOccurrenceSlots_length,
      directSourceFinalVariableFanData_length]
  have clauseLength : clauses.length = fans.length := by
    rw [← clausesEq, ← fanDataEq,
      directSourceFinalClauseFrames_length,
      directSourceFinalVariableFanData_length]
  simpa only [List.map_map, Function.comp_def,
    DirectFinalOccurrenceFrame.codeOfData] using
    (AlignedThreeNatColumns.zip_map_add
      DirectFinalOccurrenceFrame.variableFanBase
      DirectFinalOccurrenceFrame.occurrenceSlotValue
      DirectFinalOccurrenceFrame.clauseFrameBase
      fans slots clauses slotLength clauseLength)

end LeanTrominoes.PeriodicCNFStripReduction

end
