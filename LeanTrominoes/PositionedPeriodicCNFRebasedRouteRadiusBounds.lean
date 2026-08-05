import LeanTrominoes.OrthogonalPolylineCoordinateRadiusBounds
import LeanTrominoes.PositionedPeriodicCNFRebasedRouteBounds
import LeanTrominoes.PositionedPeriodicCNFRebasedRouteTransport
import LeanTrominoes.PositionedPeriodicCNFVariableGaugeClauseMembership
import LeanTrominoes.RetainedRayRasterizationCorridor

/-!
# Radius criteria for rebased incidence-route halo bounds

A rebased route starts at its variable representative.  If that
representative is in the fundamental square and every route point is at
coordinate distance at most one period from it, then the complete route is
automatically in the open one-period halo.  This module packages that small
arithmetic bridge in the form used by the final Figure 9 coordinate proof.
-/

namespace LeanTrominoes

open PeriodicEightOccurrenceSplit

namespace PeriodicGridDrawing

/-- A point within one period, coordinatewise, of a fundamental-square
center lies in the open one-period halo. -/
theorem positionInExpandedSquare_of_withinCoordinateRadius
    (drawing : PeriodicGridDrawing)
    {radius : Nat} {center point : Cell}
    (centerInside : drawing.PositionInFundamentalSquare center)
    (radiusLe : radius ≤ drawing.gridSize)
    (bounded : WithinCoordinateRadius radius center point) :
    drawing.PositionInExpandedSquare point := by
  have horizontalAbsolute :
      |point.1 - center.1| ≤ (radius : Int) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast bounded.1
  have verticalAbsolute :
      |point.2 - center.2| ≤ (radius : Int) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast bounded.2
  have horizontal := (abs_le.mp horizontalAbsolute)
  have vertical := (abs_le.mp verticalAbsolute)
  have radiusLeInt : (radius : Int) ≤ drawing.gridSize := by
    exact_mod_cast radiusLe
  have periodPositive : (0 : Int) < drawing.gridSize := by
    exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  simp only [PositionInFundamentalSquare] at centerInside
  simp only [PositionInExpandedSquare]
  omega

end PeriodicGridDrawing

namespace PositionedPeriodicCNF

/-- Every point of every rebased genuine incidence route is within one
physical period, coordinatewise, of that incidence's variable prototype. -/
def PlanarIncidencePresentation.RebasedRoutePointsWithinVariablePeriod
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : PlanarIncidencePresentation source placement) : Prop :=
  ∀ tagged ∈
      (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx,
    ∀ point ∈ presentation.variableToClauseRoute tagged.1,
      WithinCoordinateRadius placement.period
        (placement.position tagged.1.literal.atom) point

/-- Pointwise, membership-based form of the variable-centered radius bound.
Unlike a planar presentation, this predicate needs only a positioned formula,
placement, and raw route family, so it can be transported through intermediate
presentation changes before compatibility has been packaged. -/
def RebasedIncidenceRoutesWithinVariablePeriod
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes) : Prop :=
  ∀ clause clauseIndex,
    (clause, clauseIndex) ∈ source.clauses.zipIdx →
    ∀ literal literalIndex,
      (literal, literalIndex) ∈ clause.literals.zipIdx →
      ∀ point ∈
        PeriodicOrthocrossing.translatePolyline
          (placement.translation
            (Cell.sub
              (PeriodicCNF.clauseAnchor clause.literals)
              literal.offset))
          (routes clauseIndex literalIndex).reverse,
        WithinCoordinateRadius placement.period
          (placement.position literal.atom) point

/-- The rebased variable-centered certificate can equivalently be read on
the stored physical route: every raw point is within one period of that
incidence's canonical clause-anchor-gauged literal endpoint. -/
theorem RebasedIncidenceRoutesWithinVariablePeriod.rawRoutePointsWithinCanonicalLiteralPeriod
    {Variable : Type*}
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    {routes : IncidenceRoutes}
    (bounds :
      RebasedIncidenceRoutesWithinVariablePeriod
        source placement routes)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ source.clauses.zipIdx)
    {literal : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    {point : Cell}
    (pointMember : point ∈ routes clauseIndex literalIndex) :
    WithinCoordinateRadius placement.period
      (canonicalLiteralPosition placement clause literal)
      point := by
  let shift :=
    placement.translation
      (Cell.sub
        (PeriodicCNF.clauseAnchor clause.literals)
        literal.offset)
  have rebasedMember :
      Cell.add shift point ∈
        PeriodicOrthocrossing.translatePolyline shift
          (routes clauseIndex literalIndex).reverse := by
    unfold PeriodicOrthocrossing.translatePolyline
    exact List.mem_map.mpr
      ⟨point, List.mem_reverse.mpr pointMember, rfl⟩
  have rebasedBounded :=
    bounds clause clauseIndex clauseMember
      literal literalIndex literalMember
      (Cell.add shift point) rebasedMember
  have translated := rebasedBounded.translate
    (Cell.scale (-1) shift)
  simpa [shift, canonicalLiteralPosition,
    PeriodicVariablePlacement.translation,
    Cell.add, Cell.sub, Cell.scale,
    sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    using translated

/-- The raw membership-based radius certificate supplies the corresponding
field of any planar presentation with that route family. -/
theorem PlanarIncidencePresentation.rebasedRoutePointsWithinVariablePeriod_of_raw
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : PlanarIncidencePresentation source placement)
    (bounds :
      RebasedIncidenceRoutesWithinVariablePeriod
        source placement presentation.routes) :
    presentation.RebasedRoutePointsWithinVariablePeriod := by
  intro tagged taggedMember point pointMember
  rcases incidenceMetadata_of_tagged source taggedMember with
    ⟨clause, literal, clauseMember, literalMember, incidenceEq⟩
  rw [incidenceEq] at pointMember ⊢
  exact bounds clause tagged.1.clauseIndex clauseMember
    literal tagged.1.literalIndex literalMember point pointMember

/-- Stable clause reindexing and its canonical anchor translation preserve
the raw variable-centered radius certificate. -/
theorem RebasedIncidenceRoutesWithinVariablePeriod.orderCanonicalRoutesByClauseDirection
    {Variable : Type*}
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    {routes : IncidenceRoutes}
    (bounds :
      RebasedIncidenceRoutesWithinVariablePeriod
        source placement routes) :
    RebasedIncidenceRoutesWithinVariablePeriod
      (orderClausesByRouteDirection source routes)
      placement
      (orderCanonicalRoutesByClauseDirection
        source placement routes) := by
  intro orderedClause clauseIndex clauseMember
    literal literalIndex literalMember point pointMember
  rcases exists_sourceLiteral_of_orderCanonicalRoutes_rebasedRoute_eq
      source placement routes clauseMember literalMember with
    ⟨sourceClause, sourceLiteral, sourceLiteralIndex,
      sourceClauseMember, sourceLiteralMember,
      literalEq, routeEq⟩
  subst literal
  rw [routeEq] at pointMember
  exact bounds sourceClause clauseIndex sourceClauseMember
    sourceLiteral sourceLiteralIndex sourceLiteralMember
    point pointMember

/-- Canonical route transport through a variable gauge preserves the raw
variable-centered radius certificate: both route points and their variable
center receive the same inverse physical gauge translation. -/
theorem RebasedIncidenceRoutesWithinVariablePeriod.variableGaugeCanonicalIncidenceRoutes
    {Variable : Type*}
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    {routes : IncidenceRoutes}
    (gauge : Variable → Cell)
    (bounds :
      RebasedIncidenceRoutesWithinVariablePeriod
        source placement routes) :
    RebasedIncidenceRoutesWithinVariablePeriod
      (source.variableGauge gauge)
      (placement.variableGauge gauge)
      (variableGaugeCanonicalIncidenceRoutes
        source placement gauge routes) := by
  intro gaugedClause clauseIndex gaugedClauseMember
    gaugedLiteral literalIndex gaugedLiteralMember point pointMember
  rcases exists_sourceClause_of_variableGaugeClause_mem
      source gauge gaugedClauseMember with
    ⟨sourceClause, sourceClauseMember, gaugedClauseEq⟩
  subst gaugedClause
  change
    (gaugedLiteral, literalIndex) ∈
      (sourceClause.literals.map
        (PeriodicLiteral.variableGauge gauge)).zipIdx
    at gaugedLiteralMember
  rw [List.zipIdx_map] at gaugedLiteralMember
  rcases List.mem_map.mp gaugedLiteralMember with
    ⟨taggedSourceLiteral, taggedSourceLiteralMember,
      gaugedTaggedLiteralEq⟩
  have literalIndexEq :
      taggedSourceLiteral.2 = literalIndex :=
    congrArg Prod.snd gaugedTaggedLiteralEq
  subst literalIndex
  have gaugedLiteralEq :
      gaugedLiteral =
        taggedSourceLiteral.1.variableGauge gauge :=
    (congrArg Prod.fst gaugedTaggedLiteralEq).symm
  subst gaugedLiteral
  rw [variableGaugeCanonicalIncidenceRoutes_rebasedRoute_eq
    source placement gauge routes sourceClauseMember]
    at pointMember
  unfold PeriodicOrthocrossing.translatePolyline at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨sourcePoint, sourcePointMember, rfl⟩
  have sourceBounded :=
    bounds sourceClause clauseIndex sourceClauseMember
      taggedSourceLiteral.1 taggedSourceLiteral.2
      taggedSourceLiteralMember sourcePoint sourcePointMember
  have translated := sourceBounded.translate
    (placement.translation
      (Cell.sub (0, 0) (gauge taggedSourceLiteral.1.atom)))
  simpa [PeriodicVariablePlacement.variableGauge,
    PeriodicVariablePlacement.translation,
    Cell.add, Cell.sub, Cell.scale,
    sub_eq_add_neg, add_comm] using translated

/-- Pointwise orthogonal loop erasure preserves the raw variable-centered
radius certificate.  Newly inserted unit-subdivision points remain on
radius-bounded source segments, and loop erasure only discards points. -/
theorem RebasedIncidenceRoutesWithinVariablePeriod.normalizeOrthogonalIncidenceRoutes
    {Variable : Type*}
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    {routes : IncidenceRoutes}
    (bounds :
      RebasedIncidenceRoutesWithinVariablePeriod
        source placement routes)
    (routesNonempty :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ source.clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
          routes clauseIndex literalIndex ≠ [])
    (routesOrthogonal :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ source.clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
          PeriodicOrthocrossing.OrthogonalPolyline
            (routes clauseIndex literalIndex)) :
    RebasedIncidenceRoutesWithinVariablePeriod
      source placement
      (normalizeOrthogonalIncidenceRoutes routes) := by
  intro clause clauseIndex clauseMember
    literal literalIndex literalMember point pointMember
  let shift :=
    placement.translation
      (Cell.sub
        (PeriodicCNF.clauseAnchor clause.literals)
        literal.offset)
  let route := routes clauseIndex literalIndex
  change point ∈
    PeriodicOrthocrossing.translatePolyline shift
      (AxisDirection.normalizeOrthogonalPolyline route).reverse
    at pointMember
  unfold PeriodicOrthocrossing.translatePolyline at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨normalizedPoint, normalizedPointMember, rfl⟩
  have normalizedPointMember' :
      normalizedPoint ∈
        AxisDirection.normalizeOrthogonalPolyline route := by
    simpa using normalizedPointMember
  apply
    AxisDirection.normalizeOrthogonalPolyline_points_withinCoordinateRadius
      (routesNonempty clause clauseIndex clauseMember
        literal literalIndex literalMember)
      (routesOrthogonal clause clauseIndex clauseMember
        literal literalIndex literalMember)
      shift (placement.position literal.atom)
  · intro sourcePoint sourcePointMember
    apply bounds clause clauseIndex clauseMember
      literal literalIndex literalMember
    unfold PeriodicOrthocrossing.translatePolyline
    exact List.mem_map.mpr
      ⟨sourcePoint, by simpa using sourcePointMember, rfl⟩
  · exact normalizedPointMember'

/-- The variable-centered one-period radius criterion implies the exact
rebased-route halo bound consumed by ribbon thickening. -/
theorem PlanarIncidencePresentation.rebasedRoutePointsInExpandedSquare_of_withinVariablePeriod
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : PlanarIncidencePresentation source placement)
    (bounds : presentation.RebasedRoutePointsWithinVariablePeriod) :
    presentation.RebasedRoutePointsInExpandedSquare := by
  intro tagged taggedMember point pointMember
  let drawing :=
    incidenceDrawing source placement presentation.routes
  have taggedEdgeMember :=
    PeriodicCNF.tagged_incidence_edge_mem
      source.erase taggedMember
  have targetMember :=
    (PeriodicCNF.incidenceGraph_isWellFormed source.erase).2
      tagged.1.edge (List.fst_mem_of_mem_zipIdx taggedEdgeMember) |>.2
  have variableMember :
      CNFVertex.variable tagged.1.literal.atom ∈
        source.erase.incidenceGraph.vertices := by
    simpa [CNFIncidence.edge, PeriodicCNF.incidenceEdge]
      using targetMember
  have variablePositionMember :=
    incidenceDrawing_vertexPosition_mem_of_compatible
      source placement presentation.routes presentation.compatible
      variableMember
  have variablePositionEq :=
    incidenceDrawing_vertexPosition_of_mem
      source placement presentation.routes variableMember
  have variableInside :=
    presentation.compatible.2.2.2.2.1 _ variablePositionMember
  rw [variablePositionEq] at variableInside
  change drawing.PositionInFundamentalSquare
      (placement.position tagged.1.literal.atom) at variableInside
  apply
    PeriodicGridDrawing.positionInExpandedSquare_of_withinCoordinateRadius
      drawing variableInside
  · simpa [drawing] using
      (incidenceDrawing_gridSize source placement presentation.routes
        presentation.periodPositive).symm.le
  · exact bounds tagged taggedMember point pointMember

end PositionedPeriodicCNF
end LeanTrominoes
