/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineTerminalCandidateCompiler
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierNodePositionData

/-! # Affine compilation of both terminal position coordinates -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Select either physical coordinate, independently of the carrier axis. -/
def carrierNodeCoordinateAtPeriod (horizontal : Bool)
    (period : Nat) (node : CarrierNode) : Int :=
  let position := carrierNodePositionAtPeriod period node
  if horizontal then position.1 else position.2

def carrierNodeCoordinateFieldAtPeriod (horizontal keepPositive : Bool)
    (period : Nat) (node : CarrierNode) : Nat :=
  let coordinate := carrierNodeCoordinateAtPeriod horizontal period node
  if keepPositive then coordinate.toNat else (-coordinate).toNat

namespace RouteDescriptorPairAffine

open Computability Turing

/-- Along the carrier axis the local coordinate is the directed port; the
perpendicular local coordinate is always six. -/
def terminalLocalCoordinate (coordinateHorizontal horizontal : Bool)
    (endpoint : SegmentEnd) (increasing : Bool) : Int :=
  if coordinateHorizontal = horizontal then
    terminalLocalOrderOffset endpoint increasing
  else 6

def Segment.terminalCoordinateExpression (segment : Segment)
    (coordinateHorizontal horizontal : Bool) (translate : Cell)
    (endpoint : SegmentEnd) (increasing : Bool) : Expression :=
  segment.terminalOrderExpression coordinateHorizontal translate endpoint
    (terminalLocalCoordinate coordinateHorizontal horizontal endpoint increasing)

/-- Both endpoints at each neighboring translation, in the existing
terminal candidate order. -/
def Segment.terminalCoordinateExpressionBlock (segment : Segment)
    (coordinateHorizontal horizontal increasing : Bool) : List Expression :=
  neighborTranslations.flatMap fun translate =>
    [segment.terminalCoordinateExpression coordinateHorizontal horizontal
        translate .start increasing,
      segment.terminalCoordinateExpression coordinateHorizontal horizontal
        translate .finish increasing]

def Segment.terminalCoordinateExpressionBlocks (segment : Segment)
    (coordinateHorizontal : Bool) : List (List Expression) :=
  [segment.terminalCoordinateExpressionBlock coordinateHorizontal true false,
    segment.terminalCoordinateExpressionBlock coordinateHorizontal true true,
    segment.terminalCoordinateExpressionBlock coordinateHorizontal false false,
    segment.terminalCoordinateExpressionBlock coordinateHorizontal false true]

def RouteShape.terminalCoordinateExpressionBlocks (shape : RouteShape)
    (coordinateHorizontal : Bool) : List (List Expression) :=
  (shape.segments .first).flatMap fun segment =>
    segment.terminalCoordinateExpressionBlocks coordinateHorizontal

def terminalCoordinateExpressions (coordinateHorizontal : Bool) : List Expression :=
  (allRouteShapes.flatMap fun shape =>
    shape.terminalCoordinateExpressionBlocks coordinateHorizontal).flatten

/-- Four signed coordinate columns, evaluated over the fixed affine template
family by the existing unary arithmetic machine. -/
def terminalCoordinateFields (horizontal keepPositive : Bool)
    (tokens : List RouteDescriptorPairFieldTags.Token) : List Nat :=
  normalizedFields keepPositive (terminalCoordinateExpressions horizontal) tokens

noncomputable def terminalCoordinateFieldsComputableInPolyTime
    (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (terminalCoordinateFields horizontal keepPositive) :=
  normalizedFieldsComputableInPolyTime keepPositive
    (terminalCoordinateExpressions horizontal)

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing

end
