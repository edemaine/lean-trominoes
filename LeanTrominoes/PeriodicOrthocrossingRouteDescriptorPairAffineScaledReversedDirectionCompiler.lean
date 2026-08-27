/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineDirectionCompiler

/-! # Compiling doubled reversed affine route words

The horizontal occurrence construction doubles a stored incidence route and
then reverses it.  Performing those two fixed operations on the affine segment
templates keeps the compiler entirely streaming: no dynamically sized word
has to be reversed after it is emitted.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open Computability Turing
open RouteDescriptorPairFieldTags

/-- Double one affine point about the origin. -/
def Point.scaleTwo (affinePoint : Point) : Point :=
  point (affinePoint.horizontal.scale 2) (affinePoint.vertical.scale 2)

/-- Reverse one affine segment and double both of its endpoints. -/
def Segment.scaledReverse (segment : Segment) : Segment :=
  ⟨segment.finish.scaleTwo, segment.start.scaleTwo⟩

/-- Doubled reversed segment templates of one fixed route shape. -/
def RouteShape.scaledReversedSegments
    (shape : RouteShape) (side : Side) : List Segment :=
  (shape.segments side).reverse.map Segment.scaledReverse

/-- Signed coordinate differences of the doubled reversed route shape. -/
def RouteShape.scaledReversedDirectionExpressions
    (shape : RouteShape) (side : Side) : List Expression :=
  (shape.scaledReversedSegments side).flatMap
    Segment.directionExpressions

/-- Positive unary lengths of the doubled reversed route shape. -/
def RouteShape.scaledReversedDirectionValues
    (shape : RouteShape) (side : Side)
    (tokens : List RouteDescriptorPairFieldTags.Token) : List Nat :=
  normalizedFields true
    (shape.scaledReversedDirectionExpressions side) tokens

/-- Streaming decoder output for the doubled reversed route shape. -/
def RouteShape.compiledScaledReversedDirectionWord
    (shape : RouteShape) (side : Side)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List AxisDirection :=
  UnaryFourFieldDirections.directions
    (shape.scaledReversedDirectionValues side tokens)

/-- Mathematical affine direction word of the doubled reversed shape. -/
def RouteShape.scaledReversedDirectionWord
    (shape : RouteShape) (side : Side)
    (pair : RouteDescriptor × RouteDescriptor) : List AxisDirection :=
  (shape.scaledReversedSegments side).flatMap fun segment =>
    segment.directionBlock (pairFieldValue pair)

/-- Canonical descriptor-pair tagging makes the streaming output exact. -/
@[simp] theorem
    RouteShape.compiledScaledReversedDirectionWord_descriptorPairTokens
    (shape : RouteShape) (side : Side)
    (pair : RouteDescriptor × RouteDescriptor) :
    shape.compiledScaledReversedDirectionWord side
        (descriptorPairTokens pair) =
      shape.scaledReversedDirectionWord side pair := by
  unfold RouteShape.compiledScaledReversedDirectionWord
    RouteShape.scaledReversedDirectionValues
  rw [normalizedFields_true_eq]
  unfold RouteShape.scaledReversedDirectionExpressions
  rw [directions_directionExpressions]
  have valuationEq :
      tokenFieldValue (descriptorPairTokens pair) = pairFieldValue pair := by
    funext pairSide field
    exact tokenFieldValue_descriptorPairTokens pair pairSide field
  rw [valuationEq]
  rfl

/-- Affine normalization and four-field decoding compile the doubled reversed
word without a runtime word-reversal pass. -/
noncomputable def
    RouteShape.compiledScaledReversedDirectionWordComputableInPolyTime
    (shape : RouteShape) (side : Side) :
    TM2ComputableInPolyTime id id
      (shape.compiledScaledReversedDirectionWord side) := by
  change TM2ComputableInPolyTime id id
    (fun tokens => UnaryFourFieldDirections.directions
      (normalizedFields true
        (shape.scaledReversedDirectionExpressions side) tokens))
  let normalized := normalizedFieldsComputableInPolyTime true
    (shape.scaledReversedDirectionExpressions side)
  let decoded := UnaryFourFieldDirections.computableInPolyTime
  exact TM2CompositionMachine.computableInPolyTime normalized decoded

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes

end
