/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataTerminalData
import LeanTrominoes.RetainedAngularFanFallbackCardinalGateTangentData
import LeanTrominoes.RetainedAngularFanFallbackRouteDecomposition
import LeanTrominoes.RetainedAngularFanSourceScaledSeparation

/-! # Cardinal tangent data for retained bend routes -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PlanarThreeSAT

/-- Cardinal tangent parameters of one bend route: its terminal port,
factor-four terminal length, and fully refined penultimate-segment length.
The route table determines separately on which side of the fan gate the
tangent lies. -/
structure BendRouteCardinalTangentData where
  port : Port
  scaledLength : Nat
  distance : Nat

/-- Which side of the fan's clockwise lane direction contains the source
segment immediately before a bend route's deleted terminal segment. -/
inductive BendRouteCardinalTangentOrientation
  | backward
  | forward
  deriving DecidableEq, Repr

/-- The ten corner-table routes whose final retained source segment points
in the fan's clockwise lane direction.  Every other genuine corner route
points in the opposite direction. -/
def bendRouteCardinalTangentOrientation :
    CornerPort → CornerPort → Nat → Nat →
      BendRouteCardinalTangentOrientation
  | .west, .north, 1, 1 => .forward
  | .east, .west, 0, 0 => .forward
  | .east, .west, 1, 1 => .forward
  | .east, .north, 0, 0 => .forward
  | .east, .north, 1, 1 => .forward
  | .south, .west, 0, 0 => .forward
  | .south, .west, 1, 1 => .forward
  | .south, .east, 0, 0 => .forward
  | .south, .north, 0, 0 => .forward
  | .south, .north, 1, 1 => .forward
  | _, _, _, _ => .backward

/-- Signed lane-direction displacement selected by a tangent orientation. -/
def BendRouteCardinalTangentOrientation.signedDistance
    (orientation : BendRouteCardinalTangentOrientation)
    (distance : Nat) : Int :=
  match orientation with
  | .backward => -(distance : Int)
  | .forward => distance

/-- Cardinal port of a retained terminal, with an irrelevant east fallback
for the routed-clause cases that do not occur in the corner table. -/
def retainedTerminalCompassPort : RetainedTerminalDirection → Port
  | .compass port => port
  | .routedClause _ => .east

/-- Length of the segment immediately before the deleted variable segment. -/
def bendRoutePenultimateLength
    (firstPort secondPort : CornerPort)
    (localClauseIndex literalIndex : Nat) : Nat :=
  match (gridPolylineSegments
      (cornerEqualityRoutes firstPort secondPort
        localClauseIndex literalIndex).dropLast).getLast? with
  | some segment =>
      AxisDirection.segmentLength segment.start segment.finish
  | none => 0

/-- Computed cardinal tangent parameters of one route in the finite bend
table. -/
def bendRouteCardinalTangentData
    (firstPort secondPort : CornerPort)
    (localClauseIndex literalIndex : Nat) :
    BendRouteCardinalTangentData :=
  let terminal := bendRouteTerminalData firstPort secondPort
    localClauseIndex literalIndex
  { port := retainedTerminalCompassPort terminal.1
    scaledLength := retainedAngularFanSourceClearanceFactor * terminal.2
    distance := retainedTerminalFanTotalRefinement *
      retainedAngularFanSourceClearanceFactor *
      bendRoutePenultimateLength firstPort secondPort
        localClauseIndex literalIndex }

/-- Complete local certificate needed to apply one of the two cardinal
tangent normalization theorems to a genuine finite bend-table route. -/
structure BendRouteCardinalTangentCertificate
    (firstPort secondPort : CornerPort)
    (localClauseIndex literalIndex : Nat) : Prop where
  routeLength :
    3 ≤ (cornerEqualityRoutes firstPort secondPort
      localClauseIndex literalIndex).length
  classified :
    retainedTerminalDirectionClassify
        (PeriodicThreeSATThree.routeTerminalVector
          (cornerEqualityRoutes firstPort secondPort
            localClauseIndex literalIndex)) =
      some (bendRouteTerminalData firstPort secondPort
        localClauseIndex literalIndex)
  routeSimple :
    LocalIncidenceDrawing.RouteIsSimple
      (cornerEqualityRoutes firstPort secondPort
        localClauseIndex literalIndex)
  routeOrthogonal :
    OrthogonalPolyline
      (cornerEqualityRoutes firstPort secondPort
        localClauseIndex literalIndex)
  terminalLengthPositive :
    0 < (bendRouteTerminalData firstPort secondPort
      localClauseIndex literalIndex).2
  scaledTerminalEq :
    scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor
        (bendRouteTerminalData firstPort secondPort
          localClauseIndex literalIndex) =
      (.compass
          (bendRouteCardinalTangentData firstPort secondPort
            localClauseIndex literalIndex).port,
        (bendRouteCardinalTangentData firstPort secondPort
          localClauseIndex literalIndex).scaledLength)
  cardinal :
    let port :=
      (bendRouteCardinalTangentData firstPort secondPort
        localClauseIndex literalIndex).port
    port = .north ∨ port = .east ∨ port = .south ∨ port = .west
  scaledLengthLarge :
    2 ≤ (bendRouteCardinalTangentData firstPort secondPort
      localClauseIndex literalIndex).scaledLength
  distancePositive :
    0 < (bendRouteCardinalTangentData firstPort secondPort
      localClauseIndex literalIndex).distance
  shiftStrict :
    ∀ slot : RetainedTerminalSlot,
      retainedTerminalFanOuterLaneSpacing * slot.val <
        (bendRouteCardinalTangentData firstPort secondPort
          localClauseIndex literalIndex).distance
  predecessor :
    ∀ slot : RetainedTerminalSlot,
      (retainedFallbackSourcePrefix
          (scalePolyline retainedAngularFanSourceClearanceFactor
            (cornerEqualityRoutes firstPort secondPort
              localClauseIndex literalIndex))).dropLast.getLast? =
        some
          (Cell.add
            (retainedAngularFanOuterDemand
              (retainedFallbackFanCenter
                (scalePolyline retainedAngularFanSourceClearanceFactor
                  (cornerEqualityRoutes firstPort secondPort
                    localClauseIndex literalIndex)))
              (.compass
                  (bendRouteCardinalTangentData firstPort secondPort
                    localClauseIndex literalIndex).port,
                (bendRouteCardinalTangentData firstPort secondPort
                  localClauseIndex literalIndex).scaledLength)
              slot).gate
            (Cell.scale
              ((bendRouteCardinalTangentOrientation firstPort secondPort
                localClauseIndex literalIndex).signedDistance
                  (bendRouteCardinalTangentData firstPort secondPort
                    localClauseIndex literalIndex).distance)
              (retainedTerminalFanOuterLaneStep
                (.compass
                  (bendRouteCardinalTangentData firstPort secondPort
                    localClauseIndex literalIndex).port))))

end PeriodicEightOccurrenceSplit
end LeanTrominoes
