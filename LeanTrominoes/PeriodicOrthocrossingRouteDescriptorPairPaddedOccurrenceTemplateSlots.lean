/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairOccurrenceTemplateSemantics

/-! # Fixed affine occurrence-template slots -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

/-- Pad one route shape's affine occurrence templates to the same fixed
eighty-one slots used by semantic route descriptors. -/
def RouteShape.paddedOccurrences
    (shape : RouteShape) (side : RouteDescriptorPairFieldTags.Side) :
    List (Option Occurrence) :=
  (shape.occurrences side).map some ++
    List.replicate (81 - (shape.occurrences side).length) none

/-- Every padded affine occurrence-template block has exactly eighty-one
slots. -/
@[simp] theorem RouteShape.paddedOccurrences_length
    (shape : RouteShape) (side : RouteDescriptorPairFieldTags.Side) :
    (shape.paddedOccurrences side).length = 81 := by
  unfold RouteShape.paddedOccurrences
  rw [List.length_append, List.length_map, List.length_replicate]
  exact Nat.add_sub_of_le (shape.occurrences_length_le_eightyOne side)

/-- Read the padded affine occurrence template occupying one fixed slot. -/
def RouteShape.paddedOccurrenceAtSlot
    (shape : RouteShape) (side : RouteDescriptorPairFieldTags.Side)
    (slot : Fin 81) : Option Occurrence :=
  (shape.paddedOccurrences side).get
    (Fin.cast (shape.paddedOccurrences_length side).symm slot)

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
