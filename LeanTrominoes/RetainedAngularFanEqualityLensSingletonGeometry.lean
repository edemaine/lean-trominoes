import LeanTrominoes.RetainedAngularFanOuterEscapedTailCardinalBounds
import LeanTrominoes.PlanarThreeSATEqualityLensPlacement
import LeanTrominoes.RetainedTerminalScaling

/-!
# Singleton carrier-lens source geometry

Exactly two routes in the canonical equality lens have singleton
deleted-final-point prefixes: the upper route to the first endpoint and the
lower route to the second endpoint.  In either case the terminal is cardinal,
has length at least two, and the other route in the clause stays on the
outward side of the singleton route's source gate.

This file proves that finite fact after arbitrary signed-axis placement and
positive integral source scaling.  It is the carrier-lens input to the
escaped-fan half-plane certificate.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PlanarThreeSAT

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- In one placed equality-lens clause, a selected singleton prefix has a
cardinal terminal of length at least two, and the other literal's scaled
prefix lies on or outward of the singleton prefix in that cardinal
direction. -/
theorem axisEqualityLensRoutes_singletonPrefix_partner_cardinal_lower
    (origin : Cell)
    (direction : AxisDirection)
    (span : Int)
    (spanLarge : 8 ≤ span)
    (clauseIndex firstLiteralIndex secondLiteralIndex : Nat)
    (indicesDifferent : firstLiteralIndex ≠ secondLiteralIndex)
    (secondLiteralIndexLt : secondLiteralIndex < 2)
    (singletonPrefix :
      ((axisEqualityLensDrawing
        origin direction span).routes
          clauseIndex firstLiteralIndex).dropLast.length = 1) :
    ∃ port : Port, ∃ length : Nat,
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector
            ((axisEqualityLensDrawing
              origin direction span).routes
                clauseIndex firstLiteralIndex)) =
        some (.compass port, length) ∧
      (port = .north ∨ port = .east ∨
        port = .south ∨ port = .west) ∧
      2 ≤ length ∧
      ∀ factor : Nat,
        ∀ firstPoint ∈
            (scalePolyline factor
              ((axisEqualityLensDrawing
                origin direction span).routes
                  clauseIndex firstLiteralIndex)).dropLast,
          ∀ secondPoint ∈
              (scalePolyline factor
                ((axisEqualityLensDrawing
                  origin direction span).routes
                    clauseIndex secondLiteralIndex)).dropLast,
            Cell.linearValue port.unitVector firstPoint ≤
              Cell.linearValue port.unitVector secondPoint := by
  rcases clauseIndex with (_ | _ | clauseIndex) <;>
    rcases firstLiteralIndex with
      (_ | _ | firstLiteralIndex) <;>
    rcases secondLiteralIndex with
      (_ | _ | secondLiteralIndex)
  all_goals
    simp_all [axisEqualityLensDrawing,
      EmbeddedCNFIncidenceDrawing.placeOnAxis,
      EmbeddedCNFIncidenceDrawing.orient,
      EmbeddedCNFIncidenceDrawing.translate,
      EmbeddedCNFIncidenceDrawing.mapPoints,
      horizontalEqualityLensDrawing,
      horizontalEqualityLensRoutes,
      horizontalEqualityLensUpperLeftRoute,
      horizontalEqualityLensUpperRightRoute,
      horizontalEqualityLensLowerLeftRoute,
      horizontalEqualityLensLowerRightRoute]
  · let port : Port :=
      match direction with
      | .east => .east
      | .north => .south
      | .west => .west
      | .south => .north
      | .invalid => .east
    refine ⟨port, 3, ?_, ?_, by omega, ?_⟩
    · have vectorEq :
          Cell.sub
              (Cell.add origin
                (direction.orientPoint (3, 0)))
              (Cell.add origin
                (direction.orientPoint (0, 0))) =
            Cell.scale 3
              (RetainedTerminalDirection.compass port).primitive := by
        cases direction <;>
          simp [port, AxisDirection.orientPoint,
            RetainedTerminalDirection.primitive,
            Port.unitVector, Cell.add, Cell.sub, Cell.scale]
      rw [vectorEq]
      exact retainedTerminalDirectionClassify_scale_primitive
        (RetainedTerminalDirection.compass port) (by decide)
    · cases direction <;> simp [port]
    · intro factor
      cases direction <;>
        simp [port, AxisDirection.orientPoint,
          Port.unitVector, Cell.linearValue]
      all_goals
        have factorNonnegative : (0 : Int) ≤ factor := by positivity
        nlinarith
  · let port : Port :=
      match direction with
      | .east => .west
      | .north => .north
      | .west => .east
      | .south => .south
      | .invalid => .west
    let length := (span - 6).toNat
    have lengthPositive : 0 < length := by
      dsimp [length]
      omega
    have lengthLarge : 2 ≤ length := by
      dsimp [length]
      omega
    have lengthCast : (length : Int) = span - 6 := by
      dsimp [length]
      exact Int.toNat_of_nonneg (by omega)
    refine ⟨port, length, ?_, ?_, lengthLarge, ?_⟩
    · have vectorEq :
          Cell.sub
              (Cell.add origin
                (direction.orientPoint (6, 0)))
              (Cell.add origin
                (direction.orientPoint (span, 0))) =
            Cell.scale length
              (RetainedTerminalDirection.compass port).primitive := by
          cases direction <;>
            simp [port, AxisDirection.orientPoint,
              RetainedTerminalDirection.primitive,
              Port.unitVector, Cell.add, Cell.sub,
              Cell.scale, lengthCast] <;>
            omega
      rw [vectorEq]
      exact retainedTerminalDirectionClassify_scale_primitive
        (RetainedTerminalDirection.compass port) lengthPositive
    · cases direction <;> simp [port]
    · intro factor
      cases direction <;>
        simp [port, AxisDirection.orientPoint,
          Port.unitVector, Cell.linearValue]
      all_goals
        have factorNonnegative : (0 : Int) ≤ factor := by positivity
        nlinarith

end PeriodicEightOccurrenceSplit
end LeanTrominoes
