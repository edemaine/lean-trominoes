/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedRoutedIncidenceKeySemantics

/-! # Occurrence-block semantics of grouped routed-incidence keys -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

private theorem zipWith_repeatedBases_flatMap
    (starts : List Nat) (data : List FinalFanOccurrenceData)
    (aligned : starts.length = data.length) :
    List.zipWith (· + ·)
        (UnaryFieldFixedCopies.values 3
          (UnaryFieldConstantScale.values 3 starts))
        (data.flatMap directFinalOccurrenceRoutedIncidenceKeyOffsets) =
      (List.zipWith
        (fun start datum =>
          (directFinalOccurrenceRoutedIncidenceKeyOffsets datum).map
            fun offset => start * 3 + offset)
        starts data).flatten := by
  induction starts generalizing data with
  | nil =>
      cases data <;> simp_all [UnaryFieldFixedCopies.values,
        UnaryFieldConstantScale.values]
  | cons start starts induction =>
      cases data with
      | nil => simp at aligned
      | cons datum data =>
          have tailAligned : starts.length = data.length := by
            simpa using aligned
          rcases datum with ⟨atomControl, kind, polarity, direction⟩
          cases kind <;>
            simp [UnaryFieldFixedCopies.values,
              UnaryFieldConstantScale.values,
              directFinalOccurrenceRoutedIncidenceKeyOffsets] <;>
            simpa [UnaryFieldFixedCopies.values,
              UnaryFieldConstantScale.values,
              directFinalOccurrenceRoutedIncidenceKeyOffsets] using
                induction data tailAligned

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The global routed-incidence keys are three explicit scaled local offsets
per grouped occurrence, ordered occurrence-major and RGB-minor. -/
theorem directSourceFinalGroupedRoutedIncidenceKeys_eq_occurrenceBlocks
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedRoutedIncidenceKeys decider symbols =
      (List.zipWith
        (fun start data =>
          (directFinalOccurrenceRoutedIncidenceKeyOffsets data).map
            fun offset => start * 3 + offset)
        (directSourceFinalGroupedOccurrenceTripleBlockStarts decider symbols)
        (directSourceFinalGroupedOccurrenceData decider symbols)).flatten := by
  rw [directSourceFinalGroupedRoutedIncidenceKeys_eq_zipWith]
  unfold directSourceFinalGroupedOccurrenceRepeatedIncidenceKeyBases
    directSourceFinalGroupedOccurrenceRoutedIncidenceKeyOffsets
  exact zipWith_repeatedBases_flatMap _ _ (by simp)

end LeanTrominoes.PeriodicCNFStripReduction

end
