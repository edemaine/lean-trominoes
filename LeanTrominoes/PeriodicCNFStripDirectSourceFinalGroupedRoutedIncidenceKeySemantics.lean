/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedRoutedIncidenceKeyCompiler
import LeanTrominoes.UnaryAlignedAddSemantics

/-! # Semantics of grouped routed-incidence keys -/

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The arithmetic compiler is exactly pointwise addition of the repeated
global block bases and finite local routed-incidence offsets. -/
theorem directSourceFinalGroupedRoutedIncidenceKeys_eq_zipWith
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedRoutedIncidenceKeys decider symbols =
      List.zipWith (· + ·)
        (directSourceFinalGroupedOccurrenceRepeatedIncidenceKeyBases
          decider symbols)
        (directSourceFinalGroupedOccurrenceRoutedIncidenceKeyOffsets
          decider symbols) := by
  unfold directSourceFinalGroupedRoutedIncidenceKeys
    AlignedUnaryListClosure.added
  apply UnaryAlignedAddMachine.sums_eq_zipWith
  exact UnaryAlignedAddMachine.Valid.of_length_eq (by rw [
    directSourceFinalGroupedOccurrenceRepeatedIncidenceKeyBases_length,
    directSourceFinalGroupedOccurrenceRoutedIncidenceKeyOffsets_length])

@[simp] theorem directSourceFinalGroupedRoutedIncidenceKeys_length
    (symbols : List encoding.Γ) :
    (directSourceFinalGroupedRoutedIncidenceKeys decider symbols).length =
      3 * (directSourceFinalGroupedOccurrenceData decider symbols).length := by
  rw [directSourceFinalGroupedRoutedIncidenceKeys_eq_zipWith,
    List.length_zipWith,
    directSourceFinalGroupedOccurrenceRepeatedIncidenceKeyBases_length,
    directSourceFinalGroupedOccurrenceRoutedIncidenceKeyOffsets_length,
    min_self]

end LeanTrominoes.PeriodicCNFStripReduction
