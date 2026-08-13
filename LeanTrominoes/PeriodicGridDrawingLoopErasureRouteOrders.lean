/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicGridDrawingLoopErasure
import LeanTrominoes.RetainedAngularFanFinalCoordinatedTerminalDirections
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceClauseRouteOrder

/-!
# Route orders through orthogonal loop erasure

Ribbon source fans depend only on the first direction of each clause route
and the last direction of each variable route.  Loop erasure need not preserve
those directions for an arbitrary walk: an endpoint may already occur in the
interior.  For a geometrically simple route, however, normalization is exactly
unit subdivision, so both directions survive.  This module lifts that fact to
the two route-order predicates used by the ribbon construction.
-/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

/-- A nondegenerate orthogonal route remains nondegenerate after ordered
unit subdivision. -/
private theorem unitSubdividePolyline_length_ge_two_of_length_ge_two
    {points : List Cell}
    (length : 2 ≤ points.length)
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points) :
    2 ≤ (AxisDirection.unitSubdividePolyline points).length := by
  cases points with
  | nil => simp at length
  | cons first rest =>
      cases rest with
      | nil => simp at length
      | cons second rest =>
          exact
            AxisDirection.unitSubdividePolyline_length_ge_two
              (first := first) (second := second)
              (rest := rest) orthogonal

/-- Canonical ternary-clause route order transfers between route families
whose initial directions agree on every genuine positioned incidence. -/
theorem TernaryClauseRoutesInUnitEliminationOrder.of_memberwise_firstDirection_eq
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {firstRoutes secondRoutes : IncidenceRoutes}
    (ordered :
      source.TernaryClauseRoutesInUnitEliminationOrder firstRoutes)
    (directions :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ source.clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
          AxisDirection.polylineFirstDirection
              (secondRoutes clauseIndex literalIndex) =
            AxisDirection.polylineFirstDirection
              (firstRoutes clauseIndex literalIndex)) :
    source.TernaryClauseRoutesInUnitEliminationOrder secondRoutes := by
  intro indexed indexedMember arity
  rcases incidenceMetadata_of_tagged source indexedMember with
    ⟨clause, literal, clauseMember, literalMember, _⟩
  rw [directions clause indexed.1.clauseIndex clauseMember
    literal indexed.1.literalIndex literalMember]
  exact ordered indexed indexedMember arity

/-- Normalizing memberwise simple, nondegenerate orthogonal routes preserves
clockwise variable occurrence order. -/
theorem VariableRoutesInOccurrenceOrder.normalizeOrthogonalIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {routes : IncidenceRoutes}
    (ordered : source.VariableRoutesInOccurrenceOrder routes)
    (lengths :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ source.clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
          2 ≤ (routes clauseIndex literalIndex).length)
    (orthogonal :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ source.clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
          PeriodicOrthocrossing.OrthogonalPolyline
            (routes clauseIndex literalIndex))
    (simple :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ source.clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
          LocalIncidenceDrawing.RouteIsSimple
            (routes clauseIndex literalIndex)) :
    source.VariableRoutesInOccurrenceOrder
      (PositionedPeriodicCNF.normalizeOrthogonalIncidenceRoutes routes) := by
  apply ordered.of_memberwise_lastDirection_eq
  intro clause clauseIndex clauseMember
    literal literalIndex literalMember
  exact
    AxisDirection.polylineLastDirection_normalizeOrthogonalPolyline_of_simple
      (lengths clause clauseIndex clauseMember
        literal literalIndex literalMember)
      (orthogonal clause clauseIndex clauseMember
        literal literalIndex literalMember)
      (simple clause clauseIndex clauseMember
        literal literalIndex literalMember)

/-- Normalizing memberwise simple, nondegenerate orthogonal routes preserves
the canonical order at every ternary unit-elimination clause. -/
theorem
    TernaryClauseRoutesInUnitEliminationOrder.normalizeOrthogonalIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {routes : IncidenceRoutes}
    (ordered :
      source.TernaryClauseRoutesInUnitEliminationOrder routes)
    (lengths :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ source.clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
          2 ≤ (routes clauseIndex literalIndex).length)
    (orthogonal :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ source.clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
          PeriodicOrthocrossing.OrthogonalPolyline
            (routes clauseIndex literalIndex))
    (simple :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ source.clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
          LocalIncidenceDrawing.RouteIsSimple
            (routes clauseIndex literalIndex)) :
    source.TernaryClauseRoutesInUnitEliminationOrder
      (PositionedPeriodicCNF.normalizeOrthogonalIncidenceRoutes routes) := by
  apply ordered.of_memberwise_firstDirection_eq
  intro clause clauseIndex clauseMember
    literal literalIndex literalMember
  exact
    AxisDirection.polylineFirstDirection_normalizeOrthogonalPolyline_of_simple
      (lengths clause clauseIndex clauseMember
        literal literalIndex literalMember)
      (orthogonal clause clauseIndex clauseMember
        literal literalIndex literalMember)
      (simple clause clauseIndex clauseMember
        literal literalIndex literalMember)

/-- Clockwise variable occurrence order survives loop erasure even when
routes have interior loops, provided no unit-subdivided route reaches its
target endpoint before its final point. -/
theorem
    VariableRoutesInOccurrenceOrder.normalizeOrthogonalIncidenceRoutes_of_lastNotInDropLast
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {routes : IncidenceRoutes}
    (ordered : source.VariableRoutesInOccurrenceOrder routes)
    (lengths :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ source.clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
          2 ≤ (routes clauseIndex literalIndex).length)
    (orthogonal :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ source.clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
          PeriodicOrthocrossing.OrthogonalPolyline
            (routes clauseIndex literalIndex))
    (targetFresh :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ source.clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
          AxisDirection.LastNotInDropLast
            (AxisDirection.unitSubdividePolyline
              (routes clauseIndex literalIndex))) :
    source.VariableRoutesInOccurrenceOrder
      (PositionedPeriodicCNF.normalizeOrthogonalIncidenceRoutes routes) := by
  apply ordered.of_memberwise_lastDirection_eq
  intro clause clauseIndex clauseMember
    literal literalIndex literalMember
  have routeOrthogonal :=
    orthogonal clause clauseIndex clauseMember
      literal literalIndex literalMember
  exact
    AxisDirection.polylineLastDirection_normalizeOrthogonalPolyline_of_lastNotInDropLast
      (unitSubdividePolyline_length_ge_two_of_length_ge_two
        (lengths clause clauseIndex clauseMember
          literal literalIndex literalMember)
        routeOrthogonal)
      routeOrthogonal
      (targetFresh clause clauseIndex clauseMember
        literal literalIndex literalMember)

/-- Canonical ternary-clause route order survives loop erasure even when
routes have interior loops, provided no unit-subdivided route returns to its
clause endpoint after leaving it. -/
theorem
    TernaryClauseRoutesInUnitEliminationOrder.normalizeOrthogonalIncidenceRoutes_of_headNotInTail
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {routes : IncidenceRoutes}
    (ordered :
      source.TernaryClauseRoutesInUnitEliminationOrder routes)
    (lengths :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ source.clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
          2 ≤ (routes clauseIndex literalIndex).length)
    (orthogonal :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ source.clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
          PeriodicOrthocrossing.OrthogonalPolyline
            (routes clauseIndex literalIndex))
    (sourceFresh :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ source.clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
          AxisDirection.HeadNotInTail
            (AxisDirection.unitSubdividePolyline
              (routes clauseIndex literalIndex))) :
    source.TernaryClauseRoutesInUnitEliminationOrder
      (PositionedPeriodicCNF.normalizeOrthogonalIncidenceRoutes routes) := by
  apply ordered.of_memberwise_firstDirection_eq
  intro clause clauseIndex clauseMember
    literal literalIndex literalMember
  have routeOrthogonal :=
    orthogonal clause clauseIndex clauseMember
      literal literalIndex literalMember
  exact
    AxisDirection.polylineFirstDirection_normalizeOrthogonalPolyline_of_headNotInTail
      (unitSubdividePolyline_length_ge_two_of_length_ge_two
        (lengths clause clauseIndex clauseMember
          literal literalIndex literalMember)
        routeOrthogonal)
      routeOrthogonal
      (sourceFresh clause clauseIndex clauseMember
        literal literalIndex literalMember)

/-- Both ribbon route-order premises survive one pointwise normalization. -/
theorem ribbonRouteOrders_normalizeOrthogonalIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {routes : IncidenceRoutes}
    (orders :
      source.VariableRoutesInOccurrenceOrder routes ∧
        source.TernaryClauseRoutesInUnitEliminationOrder routes)
    (lengths :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ source.clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
          2 ≤ (routes clauseIndex literalIndex).length)
    (orthogonal :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ source.clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
          PeriodicOrthocrossing.OrthogonalPolyline
            (routes clauseIndex literalIndex))
    (simple :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ source.clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
          LocalIncidenceDrawing.RouteIsSimple
            (routes clauseIndex literalIndex)) :
    source.VariableRoutesInOccurrenceOrder
        (PositionedPeriodicCNF.normalizeOrthogonalIncidenceRoutes routes) ∧
      source.TernaryClauseRoutesInUnitEliminationOrder
        (PositionedPeriodicCNF.normalizeOrthogonalIncidenceRoutes routes) := by
  exact
    ⟨orders.1.normalizeOrthogonalIncidenceRoutes lengths orthogonal simple,
      orders.2.normalizeOrthogonalIncidenceRoutes lengths orthogonal simple⟩

/-- Both ribbon route-order premises survive pointwise loop erasure under
the weaker endpoint-isolation conditions, without requiring the source
routes themselves to be simple. -/
theorem
    ribbonRouteOrders_normalizeOrthogonalIncidenceRoutes_of_endpointIsolation
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {routes : IncidenceRoutes}
    (orders :
      source.VariableRoutesInOccurrenceOrder routes ∧
        source.TernaryClauseRoutesInUnitEliminationOrder routes)
    (lengths :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ source.clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
          2 ≤ (routes clauseIndex literalIndex).length)
    (orthogonal :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ source.clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
          PeriodicOrthocrossing.OrthogonalPolyline
            (routes clauseIndex literalIndex))
    (sourceFresh :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ source.clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
          AxisDirection.HeadNotInTail
            (AxisDirection.unitSubdividePolyline
              (routes clauseIndex literalIndex)))
    (targetFresh :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ source.clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
          AxisDirection.LastNotInDropLast
            (AxisDirection.unitSubdividePolyline
              (routes clauseIndex literalIndex))) :
    source.VariableRoutesInOccurrenceOrder
        (PositionedPeriodicCNF.normalizeOrthogonalIncidenceRoutes routes) ∧
      source.TernaryClauseRoutesInUnitEliminationOrder
        (PositionedPeriodicCNF.normalizeOrthogonalIncidenceRoutes routes) := by
  exact
    ⟨orders.1.normalizeOrthogonalIncidenceRoutes_of_lastNotInDropLast
        lengths orthogonal targetFresh,
      orders.2.normalizeOrthogonalIncidenceRoutes_of_headNotInTail
        lengths orthogonal sourceFresh⟩

end PositionedPeriodicCNF
end LeanTrominoes
