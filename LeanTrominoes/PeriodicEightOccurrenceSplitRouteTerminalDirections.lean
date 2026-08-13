/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineEndpointDirections
import LeanTrominoes.PeriodicEightOccurrenceSplitAngularSplicedRoutes

/-!
# Terminal directions of fixed-eight occurrence-splitting routes

The clockwise Figure 7 certificate is stated using the final directed edge
of each local spoke or implication route.  This file proves that the actual
positioned routes used by occurrence splitting retain those local terminal
directions:

* translating a spoke into an atom's macrocell and periodic occurrence does
  not change its final direction;
* joining any boundary-reaching prefix to that nondegenerate spoke does not
  change its final direction; and
* translating a local implication route into an atom's macrocell does not
  change its final direction.
-/

namespace LeanTrominoes
namespace OccurrenceSplitRing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned

/-- Positioning a local spoke in an atom's macrocell preserves its final
directed axis. -/
@[simp]
theorem angularFanSpokeRoute_lastDirection
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) (index : Nat) :
    AxisDirection.polylineLastDirection
        (angularFanSpokeRoute sourcePlacement atom index) =
      AxisDirection.polylineLastDirection
        (spokeRoute (angularPortOfIndex index)) := by
  change
    AxisDirection.polylineLastDirection
        (PeriodicOrthocrossing.translatePolyline
          (macroOrigin sourcePlacement atom)
          (spokeRoute (angularPortOfIndex index))) =
      _
  exact
    AxisDirection.polylineLastDirection_translatePolyline
      _ _

/-- Lifting a positioned spoke to a periodic occurrence preserves the same
local terminal direction. -/
@[simp]
theorem angularFanSpokeRouteAt_lastDirection
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) (logicalOffset : Cell)
    (index : Nat) :
    AxisDirection.polylineLastDirection
        (angularFanSpokeRouteAt sourcePlacement
          atom logicalOffset index) =
      AxisDirection.polylineLastDirection
        (spokeRoute (angularPortOfIndex index)) := by
  change
    AxisDirection.polylineLastDirection
        (PeriodicOrthocrossing.translatePolyline
          ((PeriodicEightOccurrenceSplitPositioned.placement
            sourcePlacement).translation logicalOffset)
          (angularFanSpokeRoute sourcePlacement atom index)) =
      _
  rw [AxisDirection.polylineLastDirection_translatePolyline]
  exact angularFanSpokeRoute_lastDirection
    sourcePlacement atom index

/-- Translation preserves the number of points in a lifted spoke. -/
@[simp]
theorem angularFanSpokeRouteAt_length
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) (logicalOffset : Cell)
    (index : Nat) :
    (angularFanSpokeRouteAt sourcePlacement
      atom logicalOffset index).length =
        (spokeRoute (angularPortOfIndex index)).length := by
  simp [angularFanSpokeRouteAt,
    angularFanSpokeRoute]

/-- Every lifted local spoke contains a genuine final edge. -/
theorem angularFanSpokeRouteAt_length_ge_two
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) (logicalOffset : Cell)
    (index : Nat) :
    2 ≤
      (angularFanSpokeRouteAt sourcePlacement
        atom logicalOffset index).length := by
  rw [angularFanSpokeRouteAt_length]
  generalize portEquation :
    angularPortOfIndex index = port
  cases port <;> simp [spokeRoute]

end OccurrenceSplitRing

namespace PeriodicEightOccurrenceSplitPositioned

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

/-- The certified angular suffix has the terminal direction of its selected
local spoke. -/
@[simp]
theorem angularOccurrenceSuffix_lastDirection
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (order : OccurrenceOrder source.erase)
    (clause : PositionedPeriodicClause Variable)
    (literal : PeriodicLiteral Variable)
    (clauseIndex literalIndex : Nat) :
    AxisDirection.polylineLastDirection
        (angularOccurrenceSuffix sourcePlacement order
          clause literal clauseIndex literalIndex) =
      AxisDirection.polylineLastDirection
        (spokeRoute
          (angularPortOfIndex
            (angularOccurrenceIndex order literal
              clauseIndex literalIndex))) := by
  exact angularFanSpokeRouteAt_lastDirection
    sourcePlacement literal.atom
    (incidenceRelativeOffset clause literal)
    (angularOccurrenceIndex order literal
      clauseIndex literalIndex)

/-- Every certified angular suffix contains a genuine final edge. -/
theorem angularOccurrenceSuffix_length_ge_two
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (order : OccurrenceOrder source.erase)
    (clause : PositionedPeriodicClause Variable)
    (literal : PeriodicLiteral Variable)
    (clauseIndex literalIndex : Nat) :
    2 ≤
      (angularOccurrenceSuffix sourcePlacement order
        clause literal clauseIndex literalIndex).length := by
  exact angularFanSpokeRouteAt_length_ge_two
    sourcePlacement literal.atom
    (incidenceRelativeOffset clause literal)
    (angularOccurrenceIndex order literal
      clauseIndex literalIndex)

/-- A boundary-reaching prefix does not change the terminal direction of
the selected local spoke. -/
theorem angularSplicedOccurrenceRoute_lastDirection
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    {order : OccurrenceOrder source.erase}
    (boundary :
      AngularBoundaryRoutes source sourcePlacement order)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ source.clauses.zipIdx)
    {literal : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    AxisDirection.polylineLastDirection
        (angularSplicedOccurrenceRoute boundary
          clause literal clauseIndex literalIndex) =
      AxisDirection.polylineLastDirection
        (spokeRoute
          (angularPortOfIndex
            (angularOccurrenceIndex order literal
              clauseIndex literalIndex))) := by
  unfold angularSplicedOccurrenceRoute
  rw [AxisDirection.polylineLastDirection_joinAtEndpoint
    (boundary.endpoints clause clauseIndex clauseMember
      literal literalIndex literalMember).2
    (angularOccurrenceSuffix_head?
      sourcePlacement order clause literal
      clauseIndex literalIndex)
    (angularOccurrenceSuffix_length_ge_two
      sourcePlacement order clause literal
      clauseIndex literalIndex)]
  exact angularOccurrenceSuffix_lastDirection
    sourcePlacement order clause literal
    clauseIndex literalIndex

/-- Positioning a certified implication route in an atom's macrocell
preserves its local terminal direction. -/
@[simp]
theorem positionedCycleRoutes_lastDirection
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable)
    (clauseIndex literalIndex : Nat) :
    AxisDirection.polylineLastDirection
        (positionedCycleRoutes sourcePlacement atom
          clauseIndex literalIndex) =
      AxisDirection.polylineLastDirection
        (cycleRoutes clauseIndex literalIndex) := by
  change
    AxisDirection.polylineLastDirection
        (PeriodicOrthocrossing.translatePolyline
          (macroOrigin sourcePlacement atom)
          (cycleRoutes clauseIndex literalIndex)) =
      _
  exact
    AxisDirection.polylineLastDirection_translatePolyline
      _ _

/-- A genuine flattened implication clause retrieves a positioned route
whose terminal direction is that of its recorded local Figure 7 route. -/
theorem allCycleRoutes_lastDirection
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable)}
    {cycleIndex : Nat}
    (clauseMember :
      (clause, cycleIndex) ∈
        (allCycleClauses source sourcePlacement).zipIdx)
    (literalIndex : Nat) :
    ∃ metadata : CycleClauseMetadata Variable,
      metadata.clause = clause ∧
      AxisDirection.polylineLastDirection
          (allCycleRoutes source sourcePlacement
            cycleIndex literalIndex) =
        AxisDirection.polylineLastDirection
          (cycleRoutes metadata.localClauseIndex
            literalIndex) := by
  rcases allCycleRoutes_of_clause_member
      source sourcePlacement clauseMember literalIndex with
    ⟨metadata, clauseEqual, routeEqual⟩
  refine ⟨metadata, clauseEqual, ?_⟩
  rw [routeEqual, positionedCycleRoutes_lastDirection]

end PeriodicEightOccurrenceSplitPositioned
end LeanTrominoes
