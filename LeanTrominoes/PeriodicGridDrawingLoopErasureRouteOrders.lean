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
      (normalizeOrthogonalIncidenceRoutes routes) := by
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
      (normalizeOrthogonalIncidenceRoutes routes) := by
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
        (normalizeOrthogonalIncidenceRoutes routes) ∧
      source.TernaryClauseRoutesInUnitEliminationOrder
        (normalizeOrthogonalIncidenceRoutes routes) := by
  exact
    ⟨orders.1.normalizeOrthogonalIncidenceRoutes lengths orthogonal simple,
      orders.2.normalizeOrthogonalIncidenceRoutes lengths orthogonal simple⟩

end PositionedPeriodicCNF
end LeanTrominoes
