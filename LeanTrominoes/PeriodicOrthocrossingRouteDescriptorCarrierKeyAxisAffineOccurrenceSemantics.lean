/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierKeyAxisDatum
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairOccurrenceTemplateEvaluationSemantics

/-! # Axis datum of an affine occurrence template -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- Every translation of a matched affine occurrence template's key has
the axis of its reconstructed source segment. -/
theorem Occurrence.axisDatum_segmentOccurrenceKey
    (descriptors : List RouteDescriptor)
    (selfIndexed : ∀ tagged ∈ descriptors.zipIdx,
      tagged.1.edgeIndex = tagged.2)
    (shape : RouteShape) (side : Side)
    (pair : RouteDescriptor × RouteDescriptor)
    (shapeMatches : shape.Matches (descriptorAt pair side))
    (descriptorMember : descriptorAt pair side ∈ descriptors)
    (occurrence : Occurrence)
    (occurrenceMember : occurrence ∈ shape.occurrences side)
    (translate : Cell) :
    RouteDescriptorCarrierKeyAxisDatum.value descriptors
        (some (PeriodicGridDrawing.SegmentOccurrenceKey
          (occurrence.evalPair side pair).1 translate)) =
      FixedAxisUnaryFields.value true
        (decide (occurrence.evalPair side pair).1.segment.IsHorizontal) := by
  exact
    RouteDescriptorCarrierKeyAxisDatum.value_some_segmentOccurrenceKey
      descriptors (occurrence.evalPair side pair).1 translate
      (occurrence.evalPair_indexed_mem descriptors selfIndexed shape side pair
        shapeMatches descriptorMember occurrenceMember)

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
