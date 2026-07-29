import LeanTrominoes.PeriodicCNFIncidenceVertexCoverage
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedDrawingCompatibility
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedRetainedRays
import LeanTrominoes.RetainedTerminalDirections

/-!
# Terminal directions of the final retained planar-SAT source

Every genuine route in the final gauged and deduplicated retained drawing is
a nondegenerate retained-ray polyline.  Consequently its backwards terminal
vector is classified by the eleven-direction vocabulary used by the local
angular adapter.

This is stronger than the previously established segmentwise retained-ray
certificate: it extracts the concrete positive terminal direction and length
seen by the stable angular occurrence sort.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 800000

open PeriodicEightOccurrenceSplit

/-- A genuine positioned-CNF incidence route occurs in the flat edge-route
list of its assembled periodic drawing. -/
private theorem incidenceRoute_mem_edgeRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        source.clauses.zipIdx)
    {literal : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    routes clauseIndex literalIndex ∈
      (PositionedPeriodicCNF.incidenceDrawing
        source placement routes).edgeRoutes := by
  change
    routes clauseIndex literalIndex ∈
      PositionedPeriodicCNF.incidenceEdgeRoutes
        source routes
  unfold PositionedPeriodicCNF.incidenceEdgeRoutes
  apply List.mem_flatMap.mpr
  refine ⟨(clause, clauseIndex), clauseMember, ?_⟩
  exact List.mem_map.mpr
    ⟨(literal, literalIndex), literalMember, rfl⟩

/-- Every genuine final retained route contains a terminal segment. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_length_ge_two
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      formula.incidenceGraph.IsWellFormed)
    (degree :
      formula.incidenceGraph.DegreeAtMost 3)
    (isLocal :
      formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    2 ≤
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        formula clauseIndex literalIndex).length := by
  apply
    PeriodicGridDrawing.route_length_ge_two_of_compatible_of_loopless
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).erase.incidenceGraph
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
        formula)
  · exact
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_isCompatible
        formula wellFormed degree isLocal clausesNonempty
  · exact
      PeriodicCNF.incidenceGraph_edgesAreLoopless
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).erase
  · exact
      incidenceRoute_mem_edgeRoutes
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula)
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
          formula)
        clauseMember literalMember

/-- Every backwards terminal vector in the final retained drawing belongs to
the exact eleven-direction vocabulary. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_terminalRay
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      formula.incidenceGraph.IsWellFormed)
    (degree :
      formula.incidenceGraph.DegreeAtMost 3)
    (isLocal :
      formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    RetainedTerminalRayVector
      (PeriodicThreeSATThree.routeTerminalVector
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
          formula clauseIndex literalIndex)) := by
  apply RetainedRayPolyline.routeTerminalVector_retained
  · exact
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_retainedRay
        formula wellFormed degree isLocal clausesNonempty
        (clause, clauseIndex) clauseMember
        (literal, literalIndex) literalMember
  · exact
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_length_ge_two
        formula wellFormed degree isLocal clausesNonempty
        clauseMember literalMember

end PeriodicOrthocrossing
end LeanTrominoes
