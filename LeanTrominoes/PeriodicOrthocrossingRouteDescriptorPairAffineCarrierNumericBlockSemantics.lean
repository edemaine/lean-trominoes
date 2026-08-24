/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorLocalShape
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorSegmentGeometry
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCarrierBlockSemantics

/-! # Numeric-route semantics of affine carrier candidate blocks -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- On the diagonal pair of a listed numeric route, the affine block is
exactly the segment-major, neighboring-translation-major semantic axis scan. -/
theorem affineCarrierSegmentBitBlock_numeric_diagonal
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (shape : RouteShape)
    (descriptor : RouteDescriptor)
    (descriptorMember :
      descriptor ∈ PeriodicCNF.numericRouteDescriptors formula)
    (shapeMatches : shape.Matches descriptor) :
    affineCarrierSegmentBitBlock
        (descriptorPairTokens (descriptor, descriptor)) =
      (gridPolylineSegments descriptor.route).flatMap fun segment =>
        neighborTranslations.map fun _ =>
          (decide segment.IsHorizontal, false) := by
  have segmentsEq :
      (shape.segments .first).map
          (fun segment => segment.evalPair (descriptor, descriptor)) =
        gridPolylineSegments descriptor.route := by
    simpa [descriptorAt] using
      shape.map_evalPair_segments .first
        (descriptor, descriptor) shapeMatches
  rw [affineCarrierSegmentBitBlock_eq_of_matches
    shape (descriptor, descriptor) rfl shapeMatches]
  · rw [← segmentsEq, List.flatMap_map]
  · intro segment segmentMember
    apply PeriodicCNF.numericRouteDescriptor_segment_axisAligned
      formula wellFormed degree isLocal descriptorMember
    rw [← segmentsEq]
    exact List.mem_map_of_mem segmentMember

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
