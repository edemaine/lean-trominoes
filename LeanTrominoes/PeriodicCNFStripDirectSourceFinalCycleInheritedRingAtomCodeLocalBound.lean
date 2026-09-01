/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCycleRingVertexSlotCompiler
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderInheritedSourceSelectionSemantics

/-! # Local occurrence bound for inherited implication-cycle ring slots -/

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open HorizontalRoutedRouteHeaderInheritedSourceSelection

/-- Inherited ring slots selected from one complete nine-clause implication
cycle, in final occurrence order. -/
def directSourceFinalLocalCycleSelectedInheritedRingVertexSlotValues :
    List Nat :=
  selectedInheritedValues
    (HorizontalRoutedRouteHeaderPresentationAtomScope.output
      FormulaShapeFixedEightDirection.cycleClauseDescriptors)
    (directSourceFinalLocalCycleRingVertexSlots.map Fin.val)

/-- The fixed cycle selects the two incident implication literals at each of
the nine ring vertices. -/
theorem directSourceFinalLocalCycleSelectedInheritedRingVertexSlotValues_eq :
    directSourceFinalLocalCycleSelectedInheritedRingVertexSlotValues =
      [8, 0, 0, 1, 1, 2, 2, 3, 4, 3, 5, 4, 6, 5, 7, 6, 7, 8] := by
  native_decide

/-- Consequently every genuine base-nine slot occurs exactly twice in one
complete implication-cycle block. -/
theorem directSourceFinalLocalCycleSelectedInheritedRingVertexSlot_count_eq_two :
    ∀ slot : DirectFinalCycleRingVertexSlot,
      directSourceFinalLocalCycleSelectedInheritedRingVertexSlotValues.count
        slot.val = 2 := by
  native_decide

end LeanTrominoes.PeriodicCNFStripReduction
