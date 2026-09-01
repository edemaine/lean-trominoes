/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListZipWithProject
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableFanCountKeySemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableFanSlotSemantics

/-! # Counts of grouped fan/slot pairs recovered from current keys -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Projecting the finite count predecessor from every grouped fan/slot pair
recovers the bounded multiplicity of its aligned current key. -/
theorem directSourceFinalGroupedVariableFanSlotCountPreds_eq_map_countPred
    (symbols : List encoding.Γ) :
    (directSourceFinalGroupedVariableFanSlots decider symbols).map
        (fun pair => pair.1.countPred) =
      (directSourceFinalUniqueFanQueryKeys decider symbols).map fun key =>
        BoundedPositiveCountPreds.boundedPositiveCountPred
          ((directSourceFinalAtomIdentityCodes decider symbols).count
            (key / 3)) := by
  rw [directSourceFinalGroupedVariableFanSlots_eq_zipWith,
    List.map_zipWith]
  rw [List.zipWith_project_left_of_length_eq
    (fun fan => fan.countPred)
    (directSourceFinalGroupedVariableFanData decider symbols)
    (directSourceFinalGroupedOccurrenceSlots decider symbols) (by
      rw [directSourceFinalGroupedVariableFanData_length,
        directSourceFinalGroupedOccurrenceSlots_length])]
  exact directSourceFinalGroupedVariableFanCountPreds_eq_map_countPred
    decider symbols

end LeanTrominoes.PeriodicCNFStripReduction

end
