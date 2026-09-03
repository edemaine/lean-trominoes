/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableFanSlotIndexSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceFrameCodeSemantics

/-! # Grouped occurrence-frame alignment -/

noncomputable section

set_option maxHeartbeats 800000

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Reading the original declarative frame at every stable grouped index
recovers exactly the grouped variable fan and active occurrence slot. -/
theorem directSourceFinalGroupedVariableFanSlots_eq_map_occurrenceFrame
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedVariableFanSlots decider symbols =
      (directSourceFinalGroupedOccurrenceIndices decider symbols).map
        fun index =>
          let frame :=
            (directSourceFinalOccurrenceFramesExpected
              decider symbols).getD index default
          (frame.variableFan,
            groupedVariableFanGenericSlot frame.occurrenceSlot) := by
  rw [directSourceFinalGroupedVariableFanSlots_eq_map_getD]
  apply List.map_congr_left
  intro index indexMember
  have indexLt : index <
      (directSourceFinalCompiledOccurrenceData decider symbols).length :=
    directSourceFinalGroupedOccurrenceIndex_lt
      decider symbols index indexMember
  have fanLt : index <
      (directSourceFinalVariableFanData decider symbols).length := by
    simpa using indexLt
  have slotLt : index <
      (directSourceFinalOccurrenceSlots decider symbols).length := by
    simpa using indexLt
  have clauseLt : index <
      (directSourceFinalClauseFrames decider symbols).length := by
    simpa using indexLt
  have frameLt : index <
      (directSourceFinalOccurrenceFramesExpected decider symbols).length := by
    unfold directSourceFinalOccurrenceFramesExpected
    simp only [List.length_map, List.length_zip]
    omega
  rw [List.getD_eq_getElem _ _ fanLt,
    List.getD_eq_getElem _ _ slotLt,
    List.getD_eq_getElem _ _ frameLt]
  unfold directSourceFinalOccurrenceFramesExpected
  simp only [List.getElem_map, List.getElem_zip]

end LeanTrominoes.PeriodicCNFStripReduction

end
