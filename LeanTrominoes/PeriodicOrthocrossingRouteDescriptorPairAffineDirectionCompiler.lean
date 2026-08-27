/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineDirectionBlocks
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineExpressionBatchCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairFieldValueSemantics
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.UnaryFourFieldDirectionCompiler

/-! # Compiling affine route-shape direction words -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open Computability Turing
open RouteDescriptorPairFieldTags

/-- All four signed coordinate differences, segment by segment, for one
fixed affine route shape. -/
def RouteShape.directionExpressions
    (shape : RouteShape) (side : Side) : List Expression :=
  (shape.segments side).flatMap Segment.directionExpressions

/-- Evaluate a fixed route shape's signed differences to positive unary
lengths on a tagged descriptor-pair block. -/
def RouteShape.directionValues
    (shape : RouteShape) (side : Side)
    (tokens : List RouteDescriptorPairFieldTags.Token) : List Nat :=
  normalizedFields true (shape.directionExpressions side) tokens

/-- Decode those four-field groups into the candidate shape's complete
cardinal-direction word. -/
def RouteShape.compiledDirectionWord
    (shape : RouteShape) (side : Side)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List AxisDirection :=
  UnaryFourFieldDirections.directions
    (shape.directionValues side tokens)

theorem directions_directionExpressions
    (valuation : Side → Fin 11 → Nat) (segments : List Segment) :
    UnaryFourFieldDirections.directions
        ((segments.flatMap Segment.directionExpressions).map
          fun expression => (expression.eval valuation).toNat) =
      segments.flatMap fun segment => segment.directionBlock valuation := by
  induction segments with
  | nil => rfl
  | cons segment segments induction =>
      rcases segment with ⟨start, finish⟩
      unfold UnaryFourFieldDirections.directions at induction
      simp [Segment.directionExpressions, Segment.directionBlock,
        UnaryFourFieldDirections.directions,
        UnaryFourFieldDirections.directionsFrom,
        UnaryFourFieldDirections.Control.direction,
        UnaryFourFieldDirections.Control.next, induction]

/-- On a canonical descriptor-pair block, the compiled affine direction word
is exactly the mathematical direction word of that shape. -/
@[simp] theorem RouteShape.compiledDirectionWord_descriptorPairTokens
    (shape : RouteShape) (side : Side)
    (pair : RouteDescriptor × RouteDescriptor) :
    shape.compiledDirectionWord side (descriptorPairTokens pair) =
      shape.directionWord side pair := by
  unfold RouteShape.compiledDirectionWord RouteShape.directionValues
  rw [normalizedFields_true_eq]
  unfold RouteShape.directionExpressions
  rw [directions_directionExpressions]
  have valuationEq :
      tokenFieldValue (descriptorPairTokens pair) = pairFieldValue pair := by
    funext pairSide field
    exact tokenFieldValue_descriptorPairTokens pair pairSide field
  rw [valuationEq]
  rfl

/-- For a fixed shape and side, affine normalization followed by four-field
direction decoding is a polynomial-time compiler. -/
noncomputable def RouteShape.compiledDirectionWordComputableInPolyTime
    (shape : RouteShape) (side : Side) :
    TM2ComputableInPolyTime id id
      (shape.compiledDirectionWord side) := by
  change TM2ComputableInPolyTime id id
    (fun tokens => UnaryFourFieldDirections.directions
      (normalizedFields true (shape.directionExpressions side) tokens))
  let normalized := normalizedFieldsComputableInPolyTime true
    (shape.directionExpressions side)
  let decoded := UnaryFourFieldDirections.computableInPolyTime
  exact TM2CompositionMachine.computableInPolyTime normalized decoded

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes

end
