/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedRoutedIncidenceKeyCompiler
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRoutedTriples

/-! # Typed meaning of grouped routed-incidence offsets -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PeriodicPlanarOneInThreeToThreeDM

/-- A direct occurrence block has exactly the width of the corresponding
typed occurrence-triple block. -/
theorem directFinalOccurrenceTripleBlockWidth_eq_typed
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (slot : PeriodicOneInThreeToThreeDM.OccurrenceSlot)
    (data : FinalFanOccurrenceData)
    (kindEq : data.kind = occurrenceConnectorKind source atom slot) :
    directFinalOccurrenceTripleBlockWidth data =
      (occurrenceTriples source atom slot).length := by
  cases kind : occurrenceConnectorKind source atom slot <;>
    simp_all [directFinalOccurrenceTripleBlockWidth, occurrenceTriples,
      allFixedRedTriples, allOrdinaryTriples]

/-- The three finite direct offsets are precisely the red, green, and blue
positions of the routed typed incidences in triple-major, RGB-minor order. -/
theorem directFinalOccurrenceRoutedIncidenceKeyOffsets_eq_typed
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (slot : PeriodicOneInThreeToThreeDM.OccurrenceSlot)
    (data : FinalFanOccurrenceData)
    (kindEq : data.kind = occurrenceConnectorKind source atom slot) :
    directFinalOccurrenceRoutedIncidenceKeyOffsets data =
      [3 * (occurrenceTriples source atom slot).idxOf
          (routedOccurrenceTriple source atom slot .red),
        3 * (occurrenceTriples source atom slot).idxOf
            (routedOccurrenceTriple source atom slot .green) + 1,
        3 * (occurrenceTriples source atom slot).idxOf
            (routedOccurrenceTriple source atom slot .blue) + 2] := by
  cases kind : occurrenceConnectorKind source atom slot <;>
    simp_all [directFinalOccurrenceRoutedIncidenceKeyOffsets,
      occurrenceTriples, routedOccurrenceTriple, allFixedRedTriples,
      allOrdinaryTriples]

end LeanTrominoes.PeriodicCNFStripReduction

end
