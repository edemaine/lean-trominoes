/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineScaling
import LeanTrominoes.OrthogonalPolylineSymmetries
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineScaledReversedDirectionCompiler
import LeanTrominoes.PeriodicThreeDMContractionPlanarity

/-! # Semantics of doubled reversed affine route words -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- Affine doubling evaluates to ordinary coordinatewise doubling. -/
@[simp] theorem Point.eval_scaleTwo
    (valuation : Side → Fin 11 → Nat) (affinePoint : Point) :
    affinePoint.scaleTwo.eval valuation =
      Cell.scale 2 (affinePoint.eval valuation) := by
  rcases affinePoint with ⟨horizontal, vertical⟩
  simp [Point.scaleTwo, Point.eval, point, Cell.scale]

/-- Reversing and doubling an affine segment commutes with evaluation. -/
@[simp] theorem Segment.eval_scaledReverse
    (valuation : Side → Fin 11 → Nat) (segment : Segment) :
    segment.scaledReverse.eval valuation =
      (GridSegment.reverse (segment.eval valuation)).scale 2 := by
  rcases segment with ⟨start, finish⟩
  simp [Segment.scaledReverse, Segment.eval, GridSegment.reverse,
    GridSegment.scale]

/-- The evaluated fixed segment-template list is exactly the segment list of
the doubled reversed semantic route. -/
theorem RouteShape.map_evalPair_scaledReversedSegments
    (shape : RouteShape) (side : Side)
    (pair : RouteDescriptor × RouteDescriptor)
    (shapeMatches : shape.Matches (descriptorAt pair side)) :
    (shape.scaledReversedSegments side).map
        (Segment.eval (pairFieldValue pair)) =
      gridPolylineSegments
        (scalePolyline 2 (descriptorAt pair side).route).reverse := by
  calc
    _ = ((shape.segments side).map
          (Segment.eval (pairFieldValue pair))).reverse.map
        (fun segment => (GridSegment.reverse segment).scale 2) := by
      simp [RouteShape.scaledReversedSegments, Function.comp_def]
    _ = (gridPolylineSegments
          (descriptorAt pair side).route).reverse.map
        (fun segment => (GridSegment.reverse segment).scale 2) := by
      have evaluated :
          (shape.segments side).map
              (Segment.eval (pairFieldValue pair)) =
            gridPolylineSegments (descriptorAt pair side).route := by
        simpa [Segment.evalPair] using
          shape.map_evalPair_segments side pair shapeMatches
      rw [evaluated]
    _ = _ := by
      rw [show
          (scalePolyline 2 (descriptorAt pair side).route).reverse =
            scalePolyline 2 (descriptorAt pair side).route.reverse by
        simp [scalePolyline]]
      rw [gridPolylineSegments_scalePolyline,
        gridPolylineSegments_reverse]
      simp [List.map_map, Function.comp_def]

/-- A matching affine shape emits the complete direction word of the doubled
stored route traversed backward. -/
theorem RouteShape.scaledReversedDirectionWord_eq
    (shape : RouteShape) (side : Side)
    (pair : RouteDescriptor × RouteDescriptor)
    (shapeMatches : shape.Matches (descriptorAt pair side))
    (aligned : ∀ segment ∈
      gridPolylineSegments (descriptorAt pair side).route,
      segment.IsAxisAligned) :
    shape.scaledReversedDirectionWord side pair =
      Gadget.unitSubdivisionDirections
        (scalePolyline 2 (descriptorAt pair side).route).reverse := by
  have orthogonal :
      OrthogonalPolyline (descriptorAt pair side).route :=
    (orthogonalPolyline_iff_segments _).2 aligned
  have scaledReversedOrthogonal :
      OrthogonalPolyline
        (scalePolyline 2 (descriptorAt pair side).route).reverse :=
    (orthogonal.scalePolyline (factor := 2) (by omega)).reverse
  have scaledReversedAligned : ∀ segment ∈
      gridPolylineSegments
        (scalePolyline 2 (descriptorAt pair side).route).reverse,
      segment.IsAxisAligned :=
    (orthogonalPolyline_iff_segments _).1 scaledReversedOrthogonal
  unfold RouteShape.scaledReversedDirectionWord
  simp only [Segment.directionBlock_eq]
  rw [← List.flatMap_map,
    shape.map_evalPair_scaledReversedSegments side pair shapeMatches]
  exact (Gadget.unitSubdivisionDirections_eq_segmentDirectionBlocks
    (scalePolyline 2 (descriptorAt pair side).route).reverse
    scaledReversedAligned).symm

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
