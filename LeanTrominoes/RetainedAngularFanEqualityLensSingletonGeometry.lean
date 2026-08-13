/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanOuterEscapedTailCardinalBounds
import LeanTrominoes.RetainedAngularFanSourceScaledSeparation
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

/-- The concrete upper singleton escape and its partner prefix have only
their common head in contact. -/
private theorem axisEqualityLensUpperSingleton_escape_head_contact
    (origin : Cell)
    (direction : AxisDirection)
    (span : Int)
    (_spanLarge : 8 ≤ span)
    (factor : Nat)
    (factorPositive : 0 < factor) :
    let port : Port :=
      match direction with
      | .east => .east
      | .north => .south
      | .west => .west
      | .south => .north
      | .invalid => .east
    let gate :=
      Cell.scale factor
        (Cell.add origin (direction.orientPoint (3, 0)))
    let escape :=
      [gate,
        Cell.add gate
          (Cell.scale retainedTerminalFanOuterSourceEscapeLength
            (oppositePort port).unitVector)]
    let partner :=
      [gate,
        Cell.scale factor
          (Cell.add origin (direction.orientPoint (3, -2))),
        Cell.scale factor
          (Cell.add origin (direction.orientPoint (span, -2)))]
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
        escape partner ∧
      PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesMeetOnlyAtHeads
        escape partner := by
  have factorPositiveInt : (0 : Int) < factor := by
    exact_mod_cast factorPositive
  dsimp
  cases direction
  all_goals
    constructor
    · unfold
        PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      constructor
      · intro firstIndex secondIndex
        fin_cases firstIndex <;> fin_cases secondIndex <;>
          simp [gridPolylineSegments, GridSegment.InteriorsMeet,
            GridSegment.OpenIntervalsOverlap,
            GridSegment.StrictlyBetween,
            GridSegment.IsHorizontal, GridSegment.IsVertical,
            retainedTerminalFanOuterSourceEscapeLength,
            AxisDirection.orientPoint, oppositePort,
            Port.unitVector, Cell.add, Cell.scale] <;>
          ring_nf at * <;>
          omega
      constructor
      · intro firstIndex secondIndex
        fin_cases firstIndex <;> fin_cases secondIndex <;>
          simp [gridPolylineSegments, GridSegment.InteriorContains,
            GridSegment.StrictlyBetween,
            GridSegment.IsHorizontal, GridSegment.IsVertical,
            retainedTerminalFanOuterSourceEscapeLength,
            AxisDirection.orientPoint, oppositePort,
            Port.unitVector, Cell.add, Cell.scale] <;>
          ring_nf at * <;>
          omega
      constructor
      · intro secondIndex firstIndex
        fin_cases secondIndex <;> fin_cases firstIndex <;>
          simp [gridPolylineSegments, GridSegment.InteriorContains,
            GridSegment.StrictlyBetween,
            GridSegment.IsHorizontal, GridSegment.IsVertical,
            retainedTerminalFanOuterSourceEscapeLength,
            AxisDirection.orientPoint, oppositePort,
            Port.unitVector, Cell.add, Cell.scale] <;>
          ring_nf at * <;>
          omega
      · intro firstIndex secondIndex pointsEqual
        fin_cases firstIndex <;> fin_cases secondIndex <;>
          simp_all [
            PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutePointIsEndpoint,
            retainedTerminalFanOuterSourceEscapeLength,
            AxisDirection.orientPoint, oppositePort,
            Port.unitVector, Cell.add, Cell.scale]
    · intro firstPoint firstMember secondPoint secondMember
        pointsEqual
      simp only [List.mem_cons, List.not_mem_nil, or_false]
        at firstMember secondMember
      rcases firstMember with rfl | rfl <;>
        rcases secondMember with rfl | rfl | rfl <;>
        simp_all [retainedTerminalFanOuterSourceEscapeLength,
          AxisDirection.orientPoint, oppositePort,
          Port.unitVector, Cell.add, Cell.scale]

/-- The concrete lower singleton escape and its partner prefix likewise have
only their common head in contact. -/
private theorem axisEqualityLensLowerSingleton_escape_head_contact
    (origin : Cell)
    (direction : AxisDirection)
    (factor : Nat)
    (factorPositive : 0 < factor) :
    let port : Port :=
      match direction with
      | .east => .west
      | .north => .north
      | .west => .east
      | .south => .south
      | .invalid => .west
    let gate :=
      Cell.scale factor
        (Cell.add origin (direction.orientPoint (6, 0)))
    let escape :=
      [gate,
        Cell.add gate
          (Cell.scale retainedTerminalFanOuterSourceEscapeLength
            (oppositePort port).unitVector)]
    let partner :=
      [gate,
        Cell.scale factor
          (Cell.add origin (direction.orientPoint (6, 1))),
        Cell.scale factor
          (Cell.add origin (direction.orientPoint (0, 1)))]
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
        escape partner ∧
      PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesMeetOnlyAtHeads
        escape partner := by
  have factorPositiveInt : (0 : Int) < factor := by
    exact_mod_cast factorPositive
  dsimp
  cases direction
  all_goals
    constructor
    · unfold
        PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      constructor
      · intro firstIndex secondIndex
        fin_cases firstIndex <;> fin_cases secondIndex <;>
          simp [gridPolylineSegments, GridSegment.InteriorsMeet,
            GridSegment.OpenIntervalsOverlap,
            GridSegment.StrictlyBetween,
            GridSegment.IsHorizontal, GridSegment.IsVertical,
            retainedTerminalFanOuterSourceEscapeLength,
            AxisDirection.orientPoint, oppositePort,
            Port.unitVector, Cell.add, Cell.scale] <;>
          ring_nf at * <;>
          omega
      constructor
      · intro firstIndex secondIndex
        fin_cases firstIndex <;> fin_cases secondIndex <;>
          simp [gridPolylineSegments, GridSegment.InteriorContains,
            GridSegment.StrictlyBetween,
            GridSegment.IsHorizontal, GridSegment.IsVertical,
            retainedTerminalFanOuterSourceEscapeLength,
            AxisDirection.orientPoint, oppositePort,
            Port.unitVector, Cell.add, Cell.scale] <;>
          ring_nf at * <;>
          omega
      constructor
      · intro secondIndex firstIndex
        fin_cases secondIndex <;> fin_cases firstIndex <;>
          simp [gridPolylineSegments, GridSegment.InteriorContains,
            GridSegment.StrictlyBetween,
            GridSegment.IsHorizontal, GridSegment.IsVertical,
            retainedTerminalFanOuterSourceEscapeLength,
            AxisDirection.orientPoint, oppositePort,
            Port.unitVector, Cell.add, Cell.scale] <;>
          ring_nf at * <;>
          omega
      · intro firstIndex secondIndex pointsEqual
        fin_cases firstIndex <;> fin_cases secondIndex <;>
          simp_all [
            PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutePointIsEndpoint,
            retainedTerminalFanOuterSourceEscapeLength,
            AxisDirection.orientPoint, oppositePort,
            Port.unitVector, Cell.add, Cell.scale]
    · intro firstPoint firstMember secondPoint secondMember
        pointsEqual
      simp only [List.mem_cons, List.not_mem_nil, or_false]
        at firstMember secondMember
      rcases firstMember with rfl | rfl <;>
        rcases secondMember with rfl | rfl | rfl <;>
        simp_all [retainedTerminalFanOuterSourceEscapeLength,
          AxisDirection.orientPoint, oppositePort,
          Port.unitVector, Cell.add, Cell.scale]

/-- Exact retained-terminal classification of the upper singleton route. -/
private theorem axisEqualityLensUpperSingleton_classified
    (origin : Cell)
    (direction : AxisDirection)
    (span : Int) :
    let port : Port :=
      match direction with
      | .east => .east
      | .north => .south
      | .west => .west
      | .south => .north
      | .invalid => .east
    retainedTerminalDirectionClassify
        (PeriodicThreeSATThree.routeTerminalVector
          ((axisEqualityLensDrawing
            origin direction span).routes 0 0)) =
      some (.compass port, 3) := by
  dsimp
  rw [show
      PeriodicThreeSATThree.routeTerminalVector
          ((axisEqualityLensDrawing
            origin direction span).routes 0 0) =
        Cell.scale 3
          (RetainedTerminalDirection.compass
            (match direction with
            | .east => .east
            | .north => .south
            | .west => .west
            | .south => .north
            | .invalid => .east)).primitive by
    cases direction <;>
      simp [axisEqualityLensDrawing,
        EmbeddedCNFIncidenceDrawing.placeOnAxis,
        EmbeddedCNFIncidenceDrawing.orient,
        EmbeddedCNFIncidenceDrawing.translate,
        EmbeddedCNFIncidenceDrawing.mapPoints,
        horizontalEqualityLensDrawing,
        horizontalEqualityLensRoutes,
        horizontalEqualityLensUpperLeftRoute,
        AxisDirection.orientPoint,
        PeriodicThreeSATThree.routeTerminalVector,
        gridPolylineSegments,
        RetainedTerminalDirection.primitive,
        Port.unitVector, Cell.add, Cell.sub, Cell.scale]]
  exact retainedTerminalDirectionClassify_scale_primitive
    _ (by decide)

/-- Exact retained-terminal classification of the lower singleton route. -/
private theorem axisEqualityLensLowerSingleton_classified
    (origin : Cell)
    (direction : AxisDirection)
    (span : Int)
    (spanLarge : 8 ≤ span) :
    let port : Port :=
      match direction with
      | .east => .west
      | .north => .north
      | .west => .east
      | .south => .south
      | .invalid => .west
    let length := (span - 6).toNat
    retainedTerminalDirectionClassify
        (PeriodicThreeSATThree.routeTerminalVector
          ((axisEqualityLensDrawing
            origin direction span).routes 1 1)) =
      some (.compass port, length) := by
  dsimp
  let length := (span - 6).toNat
  have lengthPositive : 0 < length := by
    dsimp [length]
    omega
  have lengthCast : (length : Int) = span - 6 := by
    dsimp [length]
    exact Int.toNat_of_nonneg (by omega)
  rw [show
      PeriodicThreeSATThree.routeTerminalVector
          ((axisEqualityLensDrawing
            origin direction span).routes 1 1) =
        Cell.scale length
          (RetainedTerminalDirection.compass
            (match direction with
            | .east => .west
            | .north => .north
            | .west => .east
            | .south => .south
            | .invalid => .west)).primitive by
    cases direction <;>
      simp [axisEqualityLensDrawing,
        EmbeddedCNFIncidenceDrawing.placeOnAxis,
        EmbeddedCNFIncidenceDrawing.orient,
        EmbeddedCNFIncidenceDrawing.translate,
        EmbeddedCNFIncidenceDrawing.mapPoints,
        horizontalEqualityLensDrawing,
        horizontalEqualityLensRoutes,
        horizontalEqualityLensLowerRightRoute,
        AxisDirection.orientPoint,
        PeriodicThreeSATThree.routeTerminalVector,
        gridPolylineSegments,
        RetainedTerminalDirection.primitive,
        Port.unitVector, Cell.add, Cell.sub, Cell.scale,
        lengthCast] <;>
      omega]
  exact retainedTerminalDirectionClassify_scale_primitive
    _ lengthPositive

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

/-- The half-plane fact immediately separates the complete post-escape fan
tail from the other prefix in the same placed equality-lens clause. -/
theorem
    axisEqualityLensRoutes_singletonPrefix_escapedTail_strictlyAvoid_partnerPrefix
    (origin : Cell)
    (direction : AxisDirection)
    (span : Int)
    (spanLarge : 8 ≤ span)
    (clauseIndex firstLiteralIndex secondLiteralIndex : Nat)
    (indicesDifferent : firstLiteralIndex ≠ secondLiteralIndex)
    (secondLiteralIndexLt : secondLiteralIndex < 2)
    (factor : Nat)
    (factorPositive : 0 < factor)
    (slot : RetainedTerminalSlot)
    (firstLength :
      2 ≤
        ((axisEqualityLensDrawing
          origin direction span).routes
            clauseIndex firstLiteralIndex).length)
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
      PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesStrictlyAvoidEachOther
        (retainedTerminalFanOuterCoordinatedEscapedCompleteTail
          (Cell.scale retainedTerminalFanTotalRefinement
            ((scalePolyline factor
              ((axisEqualityLensDrawing
                origin direction span).routes
                  clauseIndex firstLiteralIndex)).getLastD (0, 0)))
          (scaleRetainedTerminalData factor (.compass port, length))
          slot)
        (scalePolyline retainedTerminalFanTotalRefinement
          (scalePolyline factor
            ((axisEqualityLensDrawing
              origin direction span).routes
                clauseIndex secondLiteralIndex))).dropLast := by
  let firstRoute :=
    (axisEqualityLensDrawing
      origin direction span).routes
        clauseIndex firstLiteralIndex
  let secondRoute :=
    (axisEqualityLensDrawing
      origin direction span).routes
        clauseIndex secondLiteralIndex
  rcases
      axisEqualityLensRoutes_singletonPrefix_partner_cardinal_lower
        origin direction span spanLarge
        clauseIndex firstLiteralIndex secondLiteralIndex
        indicesDifferent secondLiteralIndexLt singletonPrefix with
    ⟨port, length, classified, cardinal, lengthLarge, partnerLower⟩
  refine ⟨port, length, classified, ?_⟩
  let center :=
    Cell.scale retainedTerminalFanTotalRefinement
      ((scalePolyline factor firstRoute).getLastD (0, 0))
  let gate :=
    (retainedAngularFanOuterDemand
      center
      (scaleRetainedTerminalData factor (.compass port, length))
      slot).gate
  have prefixEq :
      (scalePolyline retainedTerminalFanTotalRefinement
        (scalePolyline factor firstRoute)).dropLast =
          [gate] := by
    simpa [firstRoute, center, gate] using
      retainedAngularFanSourceScaledPrefix_eq_singleton_gate
        factorPositive firstRoute (.compass port, length) slot
        (by simpa [firstRoute] using firstLength)
        (by simpa [firstRoute] using classified)
        (by simpa [firstRoute] using singletonPrefix)
  have gateMember :
      gate ∈
        (scalePolyline retainedTerminalFanTotalRefinement
          (scalePolyline factor firstRoute)).dropLast := by
    rw [prefixEq]
    simp
  have gateMemberCombined := gateMember
  rw [scalePolyline_scalePolyline_nat] at gateMemberCombined
  have scaledLengthLarge :
      2 ≤ factor * length := by
    nlinarith
  have otherLower :
      ∀ point ∈
          (scalePolyline retainedTerminalFanTotalRefinement
            (scalePolyline factor secondRoute)).dropLast,
        Cell.linearValue port.unitVector gate ≤
          Cell.linearValue port.unitVector point := by
    intro point pointMember
    have pointMemberCombined := pointMember
    rw [scalePolyline_scalePolyline_nat] at pointMemberCombined
    have lower :=
      partnerLower
        (retainedTerminalFanTotalRefinement * factor)
        gate
        (by
          simpa [firstRoute] using gateMemberCombined)
        point
        (by
          simpa [secondRoute] using pointMemberCombined)
    exact lower
  simpa [firstRoute, secondRoute, center, gate,
    scaleRetainedTerminalData] using
      retainedTerminalFanOuterCoordinatedEscapedCompleteTail_strictlyAvoid_of_cardinal_of_linear_lower
        center port (factor * length) slot cardinal
        scaledLengthLarge
        (scalePolyline retainedTerminalFanTotalRefinement
          (scalePolyline factor secondRoute)).dropLast
        otherLower

/-- The rasterized 64-block escape of a singleton equality-lens route
avoids the other prefix in its clause, with their common source gate as the
only listed contact. -/
theorem
    axisEqualityLensRoutes_singletonPrefix_escape_head_contact_partnerPrefix
    (origin : Cell)
    (direction : AxisDirection)
    (span : Int)
    (spanLarge : 8 ≤ span)
    (clauseIndex firstLiteralIndex secondLiteralIndex : Nat)
    (indicesDifferent : firstLiteralIndex ≠ secondLiteralIndex)
    (secondLiteralIndexLt : secondLiteralIndex < 2)
    (factor : Nat)
    (factorPositive : 0 < factor)
    (slot : RetainedTerminalSlot)
    (firstLength :
      2 ≤
        ((axisEqualityLensDrawing
          origin direction span).routes
            clauseIndex firstLiteralIndex).length)
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
      (PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
          (retainedTerminalFanOuterRasterizedSourceEscapeCertificate
            (Cell.scale retainedTerminalFanTotalRefinement
              ((scalePolyline factor
                ((axisEqualityLensDrawing
                  origin direction span).routes
                    clauseIndex firstLiteralIndex)).getLastD (0, 0)))
            (scaleRetainedTerminalData factor (.compass port, length))
            slot).route
          (scalePolyline retainedTerminalFanTotalRefinement
            (scalePolyline factor
              ((axisEqualityLensDrawing
                origin direction span).routes
                  clauseIndex secondLiteralIndex))).dropLast ∧
        PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesMeetOnlyAtHeads
          (retainedTerminalFanOuterRasterizedSourceEscapeCertificate
            (Cell.scale retainedTerminalFanTotalRefinement
              ((scalePolyline factor
                ((axisEqualityLensDrawing
                  origin direction span).routes
                    clauseIndex firstLiteralIndex)).getLastD (0, 0)))
            (scaleRetainedTerminalData factor (.compass port, length))
            slot).route
          (scalePolyline retainedTerminalFanTotalRefinement
            (scalePolyline factor
              ((axisEqualityLensDrawing
                origin direction span).routes
                  clauseIndex secondLiteralIndex))).dropLast) := by
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
    have classified :
        retainedTerminalDirectionClassify
            (PeriodicThreeSATThree.routeTerminalVector
              ((axisEqualityLensDrawing
                origin direction span).routes 0 0)) =
          some (.compass port, 3) := by
      simpa [port] using
        axisEqualityLensUpperSingleton_classified
          origin direction span
    refine ⟨port, 3, classified, ?_⟩
    let firstRoute :=
      (axisEqualityLensDrawing
        origin direction span).routes 0 0
    let secondRoute :=
      (axisEqualityLensDrawing
        origin direction span).routes 0 1
    let center :=
      Cell.scale retainedTerminalFanTotalRefinement
        ((scalePolyline factor firstRoute).getLastD (0, 0))
    let gate :=
      (retainedAngularFanOuterDemand center
        (scaleRetainedTerminalData factor (.compass port, 3))
        slot).gate
    let combinedFactor :=
      retainedTerminalFanTotalRefinement * factor
    have combinedPositive : 0 < combinedFactor := by
      exact Nat.mul_pos
        (by native_decide : 0 < retainedTerminalFanTotalRefinement)
        factorPositive
    have prefixEq :
        (scalePolyline retainedTerminalFanTotalRefinement
          (scalePolyline factor firstRoute)).dropLast =
            [gate] := by
      simpa [firstRoute, center, gate] using
        retainedAngularFanSourceScaledPrefix_eq_singleton_gate
          factorPositive firstRoute (.compass port, 3) slot
          (by
            simp [firstRoute, axisEqualityLensDrawing,
              EmbeddedCNFIncidenceDrawing.placeOnAxis,
              EmbeddedCNFIncidenceDrawing.orient,
              EmbeddedCNFIncidenceDrawing.translate,
              EmbeddedCNFIncidenceDrawing.mapPoints,
              horizontalEqualityLensDrawing,
              horizontalEqualityLensRoutes,
              horizontalEqualityLensUpperLeftRoute])
          (by simpa [firstRoute] using classified)
          (by
            simp [firstRoute, axisEqualityLensDrawing,
              EmbeddedCNFIncidenceDrawing.placeOnAxis,
              EmbeddedCNFIncidenceDrawing.orient,
              EmbeddedCNFIncidenceDrawing.translate,
              EmbeddedCNFIncidenceDrawing.mapPoints,
              horizontalEqualityLensDrawing,
              horizontalEqualityLensRoutes,
              horizontalEqualityLensUpperLeftRoute])
    have gateEq :
        gate =
          Cell.scale combinedFactor
            (Cell.add origin (direction.orientPoint (3, 0))) := by
      have heads := congrArg List.head? prefixEq
      simpa [firstRoute, combinedFactor,
        scalePolyline_scalePolyline_nat,
        Cell.scale_scale, Nat.cast_mul,
        axisEqualityLensDrawing,
        EmbeddedCNFIncidenceDrawing.placeOnAxis,
        EmbeddedCNFIncidenceDrawing.orient,
        EmbeddedCNFIncidenceDrawing.translate,
        EmbeddedCNFIncidenceDrawing.mapPoints,
        horizontalEqualityLensDrawing,
        horizontalEqualityLensRoutes,
        horizontalEqualityLensUpperLeftRoute] using
          Option.some.inj heads.symm
    have escapeEq :
        (retainedTerminalFanOuterRasterizedSourceEscapeCertificate
          center
          (scaleRetainedTerminalData factor (.compass port, 3))
          slot).route =
            [gate,
              Cell.add gate
                (Cell.scale retainedTerminalFanOuterSourceEscapeLength
                  (oppositePort port).unitVector)] := by
      cases direction <;>
        simp [port, center, gate,
          retainedTerminalFanOuterRasterizedSourceEscapeCertificate,
          retainedTerminalFanOuterSourceEscapeRay,
          retainedTerminalFanOuterSourceEscapeLength,
          retainedTerminalFanOuterInwardRayOfLength,
          scaleRetainedTerminalData, RetainedRay.rasterize,
          compassRay, oppositePort]
    have partnerEq :
        (scalePolyline retainedTerminalFanTotalRefinement
          (scalePolyline factor secondRoute)).dropLast =
            [gate,
              Cell.scale combinedFactor
                (Cell.add origin
                  (direction.orientPoint (3, -2))),
              Cell.scale combinedFactor
                (Cell.add origin
                  (direction.orientPoint (span, -2)))] := by
      rw [gateEq]
      simp [secondRoute, combinedFactor,
        Cell.scale_scale, Nat.cast_mul,
        axisEqualityLensDrawing,
        EmbeddedCNFIncidenceDrawing.placeOnAxis,
        EmbeddedCNFIncidenceDrawing.orient,
        EmbeddedCNFIncidenceDrawing.translate,
        EmbeddedCNFIncidenceDrawing.mapPoints,
        horizontalEqualityLensDrawing,
        horizontalEqualityLensRoutes,
        horizontalEqualityLensUpperRightRoute]
    have separated :
        PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
            (retainedTerminalFanOuterRasterizedSourceEscapeCertificate
              center
              (scaleRetainedTerminalData factor (.compass port, 3))
              slot).route
            (scalePolyline retainedTerminalFanTotalRefinement
              (scalePolyline factor secondRoute)).dropLast ∧
          PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesMeetOnlyAtHeads
            (retainedTerminalFanOuterRasterizedSourceEscapeCertificate
              center
              (scaleRetainedTerminalData factor (.compass port, 3))
              slot).route
            (scalePolyline retainedTerminalFanTotalRefinement
              (scalePolyline factor secondRoute)).dropLast := by
      rw [escapeEq, partnerEq]
      rw [gateEq]
      simpa [port, gate,
        retainedTerminalFanOuterSourceEscapeLength] using
          axisEqualityLensUpperSingleton_escape_head_contact
            origin direction span spanLarge
            combinedFactor combinedPositive
    exact separated
  · let port : Port :=
      match direction with
      | .east => .west
      | .north => .north
      | .west => .east
      | .south => .south
      | .invalid => .west
    let length := (span - 6).toNat
    have classified :
        retainedTerminalDirectionClassify
            (PeriodicThreeSATThree.routeTerminalVector
              ((axisEqualityLensDrawing
                origin direction span).routes 1 1)) =
          some (.compass port, length) := by
      simpa [port, length] using
        axisEqualityLensLowerSingleton_classified
          origin direction span spanLarge
    refine ⟨port, length, classified, ?_⟩
    let firstRoute :=
      (axisEqualityLensDrawing
        origin direction span).routes 1 1
    let secondRoute :=
      (axisEqualityLensDrawing
        origin direction span).routes 1 0
    let center :=
      Cell.scale retainedTerminalFanTotalRefinement
        ((scalePolyline factor firstRoute).getLastD (0, 0))
    let gate :=
      (retainedAngularFanOuterDemand center
        (scaleRetainedTerminalData factor (.compass port, length))
        slot).gate
    let combinedFactor :=
      retainedTerminalFanTotalRefinement * factor
    have combinedPositive : 0 < combinedFactor := by
      exact Nat.mul_pos
        (by native_decide : 0 < retainedTerminalFanTotalRefinement)
        factorPositive
    have prefixEq :
        (scalePolyline retainedTerminalFanTotalRefinement
          (scalePolyline factor firstRoute)).dropLast =
            [gate] := by
      simpa [firstRoute, center, gate] using
        retainedAngularFanSourceScaledPrefix_eq_singleton_gate
          factorPositive firstRoute (.compass port, length) slot
          (by
            simp [firstRoute, axisEqualityLensDrawing,
              EmbeddedCNFIncidenceDrawing.placeOnAxis,
              EmbeddedCNFIncidenceDrawing.orient,
              EmbeddedCNFIncidenceDrawing.translate,
              EmbeddedCNFIncidenceDrawing.mapPoints,
              horizontalEqualityLensDrawing,
              horizontalEqualityLensRoutes,
              horizontalEqualityLensLowerRightRoute])
          (by simpa [firstRoute] using classified)
          (by
            simp [firstRoute, axisEqualityLensDrawing,
              EmbeddedCNFIncidenceDrawing.placeOnAxis,
              EmbeddedCNFIncidenceDrawing.orient,
              EmbeddedCNFIncidenceDrawing.translate,
              EmbeddedCNFIncidenceDrawing.mapPoints,
              horizontalEqualityLensDrawing,
              horizontalEqualityLensRoutes,
              horizontalEqualityLensLowerRightRoute])
    have gateEq :
        gate =
          Cell.scale combinedFactor
            (Cell.add origin (direction.orientPoint (6, 0))) := by
      have heads := congrArg List.head? prefixEq
      simpa [firstRoute, combinedFactor,
        scalePolyline_scalePolyline_nat,
        Cell.scale_scale, Nat.cast_mul,
        axisEqualityLensDrawing,
        EmbeddedCNFIncidenceDrawing.placeOnAxis,
        EmbeddedCNFIncidenceDrawing.orient,
        EmbeddedCNFIncidenceDrawing.translate,
        EmbeddedCNFIncidenceDrawing.mapPoints,
        horizontalEqualityLensDrawing,
        horizontalEqualityLensRoutes,
        horizontalEqualityLensLowerRightRoute] using
          Option.some.inj heads.symm
    have escapeEq :
        (retainedTerminalFanOuterRasterizedSourceEscapeCertificate
          center
          (scaleRetainedTerminalData factor (.compass port, length))
          slot).route =
            [gate,
              Cell.add gate
                (Cell.scale retainedTerminalFanOuterSourceEscapeLength
                  (oppositePort port).unitVector)] := by
      cases direction <;>
        simp [port, center, gate,
          retainedTerminalFanOuterRasterizedSourceEscapeCertificate,
          retainedTerminalFanOuterSourceEscapeRay,
          retainedTerminalFanOuterSourceEscapeLength,
          retainedTerminalFanOuterInwardRayOfLength,
          scaleRetainedTerminalData, RetainedRay.rasterize,
          compassRay, oppositePort]
    have partnerEq :
        (scalePolyline retainedTerminalFanTotalRefinement
          (scalePolyline factor secondRoute)).dropLast =
            [gate,
              Cell.scale combinedFactor
                (Cell.add origin
                  (direction.orientPoint (6, 1))),
              Cell.scale combinedFactor
                (Cell.add origin
                  (direction.orientPoint (0, 1)))] := by
      rw [gateEq]
      simp [secondRoute, combinedFactor,
        Cell.scale_scale, Nat.cast_mul,
        axisEqualityLensDrawing,
        EmbeddedCNFIncidenceDrawing.placeOnAxis,
        EmbeddedCNFIncidenceDrawing.orient,
        EmbeddedCNFIncidenceDrawing.translate,
        EmbeddedCNFIncidenceDrawing.mapPoints,
        horizontalEqualityLensDrawing,
        horizontalEqualityLensRoutes,
        horizontalEqualityLensLowerLeftRoute]
    have separated :
        PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
            (retainedTerminalFanOuterRasterizedSourceEscapeCertificate
              center
              (scaleRetainedTerminalData factor (.compass port, length))
              slot).route
            (scalePolyline retainedTerminalFanTotalRefinement
              (scalePolyline factor secondRoute)).dropLast ∧
          PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesMeetOnlyAtHeads
            (retainedTerminalFanOuterRasterizedSourceEscapeCertificate
              center
              (scaleRetainedTerminalData factor (.compass port, length))
              slot).route
            (scalePolyline retainedTerminalFanTotalRefinement
              (scalePolyline factor secondRoute)).dropLast := by
      rw [escapeEq, partnerEq]
      rw [gateEq]
      simpa [port, gate,
        retainedTerminalFanOuterSourceEscapeLength] using
          axisEqualityLensLowerSingleton_escape_head_contact
            origin direction combinedFactor combinedPositive
    exact separated

/-- Replacing a singleton equality-lens route by its complete escaped fan
route preserves separation from the other route prefix in that clause.  The
only permitted contact remains their common clause head. -/
theorem
    axisEqualityLensRoutes_singletonPrefix_escapedCompleteRoute_separated_from_partnerPrefix
    (origin : Cell)
    (direction : AxisDirection)
    (span : Int)
    (spanLarge : 8 ≤ span)
    (clauseIndex firstLiteralIndex secondLiteralIndex : Nat)
    (indicesDifferent : firstLiteralIndex ≠ secondLiteralIndex)
    (secondLiteralIndexLt : secondLiteralIndex < 2)
    (factor : Nat)
    (factorPositive : 0 < factor)
    (slot : RetainedTerminalSlot)
    (firstLength :
      2 ≤
        ((axisEqualityLensDrawing
          origin direction span).routes
            clauseIndex firstLiteralIndex).length)
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
      (PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
          (retainedTerminalFanOuterEscapedCompleteRoute
            (Cell.scale retainedTerminalFanTotalRefinement
              ((scalePolyline factor
                ((axisEqualityLensDrawing
                  origin direction span).routes
                    clauseIndex firstLiteralIndex)).getLastD (0, 0)))
            (scaleRetainedTerminalData factor (.compass port, length))
            slot)
          (scalePolyline retainedTerminalFanTotalRefinement
            (scalePolyline factor
              ((axisEqualityLensDrawing
                origin direction span).routes
                  clauseIndex secondLiteralIndex))).dropLast ∧
        PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesMeetOnlyAtHeads
          (retainedTerminalFanOuterEscapedCompleteRoute
            (Cell.scale retainedTerminalFanTotalRefinement
              ((scalePolyline factor
                ((axisEqualityLensDrawing
                  origin direction span).routes
                    clauseIndex firstLiteralIndex)).getLastD (0, 0)))
            (scaleRetainedTerminalData factor (.compass port, length))
            slot)
          (scalePolyline retainedTerminalFanTotalRefinement
            (scalePolyline factor
              ((axisEqualityLensDrawing
                origin direction span).routes
                  clauseIndex secondLiteralIndex))).dropLast) := by
  rcases
      axisEqualityLensRoutes_singletonPrefix_escapedTail_strictlyAvoid_partnerPrefix
        origin direction span spanLarge
        clauseIndex firstLiteralIndex secondLiteralIndex
        indicesDifferent secondLiteralIndexLt
        factor factorPositive slot firstLength singletonPrefix with
    ⟨tailPort, tailLength, tailClassified, tailAvoid⟩
  rcases
      axisEqualityLensRoutes_singletonPrefix_escape_head_contact_partnerPrefix
        origin direction span spanLarge
        clauseIndex firstLiteralIndex secondLiteralIndex
        indicesDifferent secondLiteralIndexLt
        factor factorPositive slot firstLength singletonPrefix with
    ⟨escapePort, escapeLength, escapeClassified,
      escapeAvoid, escapeContacts⟩
  have terminalEq :
      (RetainedTerminalDirection.compass tailPort, tailLength) =
        (.compass escapePort, escapeLength) :=
    Option.some.inj (tailClassified.symm.trans escapeClassified)
  let center :=
    Cell.scale retainedTerminalFanTotalRefinement
      ((scalePolyline factor
        ((axisEqualityLensDrawing
          origin direction span).routes
            clauseIndex firstLiteralIndex)).getLastD (0, 0))
  let partner :=
    (scalePolyline retainedTerminalFanTotalRefinement
      (scalePolyline factor
        ((axisEqualityLensDrawing
          origin direction span).routes
            clauseIndex secondLiteralIndex))).dropLast
  have escapeAvoid' :
      PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
        (retainedTerminalFanOuterRasterizedSourceEscapeCertificate
          center
          (scaleRetainedTerminalData factor
            (.compass tailPort, tailLength))
          slot).route
        partner := by
    rw [terminalEq]
    simpa [center, partner] using escapeAvoid
  have escapeContacts' :
      PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesMeetOnlyAtHeads
        (retainedTerminalFanOuterRasterizedSourceEscapeCertificate
          center
          (scaleRetainedTerminalData factor
            (.compass tailPort, tailLength))
          slot).route
        partner := by
    rw [terminalEq]
    simpa [center, partner] using escapeContacts
  refine ⟨tailPort, tailLength, tailClassified, ?_⟩
  simpa [center, partner] using
    retainedTerminalFanOuterEscapedCompleteRoute_separated_from_of_escape_head_contact
      center
      (scaleRetainedTerminalData factor
        (.compass tailPort, tailLength))
      slot partner escapeAvoid' escapeContacts'
      (by simpa [center, partner] using tailAvoid)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
