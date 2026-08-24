/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FixedAxisUnaryFields
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorLocalSegments
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorIndexedSegmentUniqueness

/-! # Carrier-key axis data recovered from route descriptors -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorCarrierKeyAxisDatum

/-- Zero for an absent candidate; otherwise the horizontal-axis bit of the
indexed segment named by the key's route and segment coordinates, with zero
as an irrelevant default for malformed keys.  Looking up the indexed segment
rather than a neighboring occurrence makes the datum independent of the
translation coordinate, including padded crossing candidates outside the
neighboring translation window. -/
noncomputable def value (descriptors : List RouteDescriptor) :
    Option CarrierKey → Nat
  | none => 0
  | some key =>
      if witness : ∃ indexed ∈ routeDescriptorIndexedSegments descriptors,
          indexed.routeIndex = key.1 ∧
            indexed.segmentIndex = key.2.1 then
        let indexed := Classical.choose witness
        FixedAxisUnaryFields.value true
          (decide indexed.segment.IsHorizontal)
      else
        0

@[simp] theorem value_none (descriptors : List RouteDescriptor) :
    value descriptors none = 0 := rfl

/-- Every reconstructed indexed segment recovers its own orientation from
the datum at any translation coordinate. -/
theorem value_some_segmentOccurrenceKey
    (descriptors : List RouteDescriptor)
    (indexed : IndexedGridSegment) (translate : Cell)
    (member : indexed ∈ routeDescriptorIndexedSegments descriptors) :
    value descriptors
        (some (PeriodicGridDrawing.SegmentOccurrenceKey indexed translate)) =
      FixedAxisUnaryFields.value true
        (decide indexed.segment.IsHorizontal) := by
  rw [value]
  split
  · rename_i witness
    let chosen := Classical.choose witness
    have chosenSpec := Classical.choose_spec witness
    have chosenSpec' :
        chosen ∈ routeDescriptorIndexedSegments descriptors ∧
          chosen.routeIndex =
            (PeriodicGridDrawing.SegmentOccurrenceKey indexed translate).1 ∧
          chosen.segmentIndex =
            (PeriodicGridDrawing.SegmentOccurrenceKey indexed translate).2.1 := by
      simpa [chosen] using chosenSpec
    have indexedEq : chosen = indexed :=
      indexedSegment_eq_of_indices_eq descriptors
        chosenSpec'.1 member
        (by simpa [
          PeriodicGridDrawing.SegmentOccurrenceKey] using chosenSpec'.2.1)
        (by simpa [
          PeriodicGridDrawing.SegmentOccurrenceKey] using chosenSpec'.2.2)
    change FixedAxisUnaryFields.value true
        (decide chosen.segment.IsHorizontal) = _
    rw [indexedEq]
  · rename_i notWitness
    exact False.elim (notWitness
      ⟨indexed, member, by
        simp [PeriodicGridDrawing.SegmentOccurrenceKey]⟩)

/-- Every listed neighboring occurrence recovers its own orientation from
the key datum. -/
theorem value_some_occurrenceKey
    (descriptors : List RouteDescriptor)
    (occurrence : IndexedGridSegment × Cell)
    (member : occurrence ∈ routeDescriptorNeighborOccurrences descriptors) :
    value descriptors (some (occurrenceKey occurrence)) =
      FixedAxisUnaryFields.value true
        (decide occurrence.1.segment.IsHorizontal) := by
  exact value_some_segmentOccurrenceKey descriptors
    occurrence.1 occurrence.2
    (indexed_mem_of_neighbor_mem descriptors member)

end RouteDescriptorCarrierKeyAxisDatum
end LeanTrominoes.PeriodicOrthocrossing

end
