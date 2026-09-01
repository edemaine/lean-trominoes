/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedNextOccurrenceKeyCompiler
import LeanTrominoes.UnaryAlignedAddSemantics

/-! # Semantics of grouped cyclic successor occurrence keys -/

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

/-- The finite successor rank always remains inside the fan's positive active
slot range. -/
theorem groupedVariableNextOccurrenceRank_lt_count
    (pair : GroupedVariableFanSlot) :
    groupedVariableNextOccurrenceRank pair < pair.1.count := by
  unfold groupedVariableNextOccurrenceRank
  apply Nat.mod_lt
  unfold VariableRibbonFanData.count
  omega

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The compiled finite successor-rank column is the direct pointwise map of
the grouped fan/slot records. -/
theorem directSourceFinalGroupedNextOccurrenceRanks_eq_map
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedNextOccurrenceRanks decider symbols =
      (directSourceFinalGroupedVariableFanSlots decider symbols).map
        groupedVariableNextOccurrenceRank := by
  rfl

/-- The final grouped key is ordinary pointwise addition of the reordered
base-three atom base and its finite cyclic successor rank. -/
theorem directSourceFinalGroupedNextOccurrenceKeys_eq_zipWith
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedNextOccurrenceKeys decider symbols =
      List.zipWith (· + ·)
        (directSourceFinalGroupedScaledAtomIdentityCodes decider symbols)
        (directSourceFinalGroupedNextOccurrenceRanks decider symbols) := by
  unfold directSourceFinalGroupedNextOccurrenceKeys
    AlignedUnaryListClosure.added
  apply UnaryAlignedAddMachine.sums_eq_zipWith
  exact UnaryAlignedAddMachine.Valid.of_length_eq (by
    rw [directSourceFinalGroupedScaledAtomIdentityCodes_length,
      directSourceFinalGroupedNextOccurrenceRanks_length])

end LeanTrominoes.PeriodicCNFStripReduction
