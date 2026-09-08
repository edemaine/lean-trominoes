/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.FiniteBlockIndexShapeSemantics
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMOccurrenceEntryIndices
import LeanTrominoes.PeriodicOneInThreeToThreeDMTaggedOccurrenceFieldLookup

/-! # Broadcast clause indices recover each occurrence's actual parent -/

namespace LeanTrominoes.PeriodicPlanarOneInThreeToThreeDM

/-- For nonempty clauses, broadcasting each clause index over its literals
is exactly the parent-index field of the tagged occurrence presentation. -/
theorem clauseParentIndices_eq_taggedLiterals
    {Variable : Type*} (source : PeriodicCNF Variable)
    (nonempty : ∀ clause ∈ source.clauses, clause ≠ []) :
    FiniteBlockIndices.expected List.length source.clauses =
      (PeriodicThreeSATThree.taggedLiterals source).map (fun tagged => tagged.2.1) := by
  unfold FiniteBlockIndices.expected
  rw [FiniteBlockIndices.expectedAux_eq_zipIdx_replicate List.length 0 source.clauses
    (fun clause member => List.length_pos_iff.mpr (nonempty clause member))]
  unfold PeriodicThreeSATThree.taggedLiterals
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro taggedClause _
  simp [List.map_map, Function.comp_def]

/-- The broadcast parent at a genuine occurrence entry is precisely the
clause index stored by that occurrence. -/
theorem clauseParentIndices_getD_of_occurrenceAt
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (nonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    (atom : Variable) (slot : OccurrenceSlot) (tagged : TaggedOccurrence Variable)
    (lookup : occurrenceAt source atom slot = some tagged) :
    (FiniteBlockIndices.expected List.length source.clauses).getD
        (occurrenceEntryIndex source (atom, slot)) 0 = tagged.2.1 := by
  rw [clauseParentIndices_eq_taggedLiterals source nonempty]
  exact PeriodicOneInThreeToThreeDM.taggedLiterals_map_getD_of_occurrenceAt
    source atom slot tagged lookup (fun item => item.2.1) 0

end LeanTrominoes.PeriodicPlanarOneInThreeToThreeDM
