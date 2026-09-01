/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectFinalOccurrenceFrameDecoderSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceFrameCodeSemantics

/-! # Semantics of complete direct final occurrence frames -/

noncomputable section

set_option maxHeartbeats 800000

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The complete decoded frame compiler is exactly the pointwise assembly of
the variable fan, stable occurrence slot, and clause-local frame columns. -/
theorem directSourceFinalOccurrenceFrames_eq_expected
    (symbols : List encoding.Γ) :
    directSourceFinalOccurrenceFrames decider symbols =
      directSourceFinalOccurrenceFramesExpected decider symbols := by
  unfold directSourceFinalOccurrenceFrames
    directSourceFinalOccurrenceFramePairs
    DirectFinalOccurrenceFrame.data
    FiniteIndexSlotUnaryDecoder.pairs
  rw [directSourceFinalOccurrenceFrameCodes_eq_expected_map,
    List.map_map]
  induction directSourceFinalOccurrenceFramesExpected decider symbols with
  | nil => rfl
  | cons frame frames induction =>
      simp only [List.map_cons, List.flatMap_cons, List.singleton_append,
        Function.comp_apply]
      rw [DirectFinalOccurrenceFrame.dataOfPair_decode_codeOfData,
        induction]

end LeanTrominoes.PeriodicCNFStripReduction

end
