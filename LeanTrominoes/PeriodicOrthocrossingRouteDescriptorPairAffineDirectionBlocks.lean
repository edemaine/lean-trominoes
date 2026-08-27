/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteSegmentDirectionBlock
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairRouteShapeSegmentSemantics

/-! # Direction words of affine route-descriptor templates -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- The four signed affine coordinate differences of one directed affine
segment, in east, north, west, south order. -/
def Segment.directionExpressions (segment : Segment) : List Expression :=
  [segment.finish.horizontal.subtract segment.start.horizontal,
    segment.finish.vertical.subtract segment.start.vertical,
    segment.start.horizontal.subtract segment.finish.horizontal,
    segment.start.vertical.subtract segment.finish.vertical]

/-- Evaluate the four signed differences and expand their positive parts as
the corresponding cardinal-direction blocks. -/
def Segment.directionBlock
    (valuation : Side → Fin 11 → Nat) (segment : Segment) :
    List AxisDirection :=
  List.replicate
      ((segment.finish.horizontal.subtract
        segment.start.horizontal).eval valuation).toNat .east ++
    List.replicate
      ((segment.finish.vertical.subtract
        segment.start.vertical).eval valuation).toNat .north ++
    List.replicate
      ((segment.start.horizontal.subtract
        segment.finish.horizontal).eval valuation).toNat .west ++
    List.replicate
      ((segment.start.vertical.subtract
        segment.finish.vertical).eval valuation).toNat .south

/-- Affine evaluation followed by signed direction expansion is exactly the
ordinary segment direction block. -/
@[simp] theorem Segment.directionBlock_eq
    (valuation : Side → Fin 11 → Nat) (segment : Segment) :
    segment.directionBlock valuation =
      Gadget.segmentDirectionBlock (segment.eval valuation) := by
  rcases segment with ⟨start, finish⟩
  simp [Segment.directionBlock, Segment.eval,
    Gadget.segmentDirectionBlock, Point.eval]

/-- Concatenate the signed direction blocks of every segment in one selected
finite affine route shape. -/
def RouteShape.directionWord
    (shape : RouteShape) (side : Side)
    (pair : RouteDescriptor × RouteDescriptor) : List AxisDirection :=
  (shape.segments side).flatMap fun segment =>
    segment.directionBlock (pairFieldValue pair)

/-- Under the exact finite shape guard, affine signed differences recover the
complete unit-subdivision direction word of the semantic descriptor route. -/
theorem RouteShape.directionWord_eq
    (shape : RouteShape) (side : Side)
    (pair : RouteDescriptor × RouteDescriptor)
    (shapeMatches : shape.Matches (descriptorAt pair side))
    (aligned : ∀ segment ∈
      gridPolylineSegments (descriptorAt pair side).route,
      segment.IsAxisAligned) :
    shape.directionWord side pair =
      Gadget.unitSubdivisionDirections (descriptorAt pair side).route := by
  unfold RouteShape.directionWord
  simp only [Segment.directionBlock_eq]
  rw [← List.flatMap_map]
  change
    (List.map (fun segment => segment.evalPair pair)
      (shape.segments side)).flatMap Gadget.segmentDirectionBlock = _
  rw [shape.map_evalPair_segments side pair shapeMatches]
  exact (Gadget.unitSubdivisionDirections_eq_segmentDirectionBlocks
    (descriptorAt pair side).route aligned).symm

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
