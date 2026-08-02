import LeanTrominoes.RetainedAngularFanFinalCoordinatedRouteValidity

/-!
# Cross-clause separation of final source routes

Distinct final source clauses give distinct tagged incidence routes.  The
inherited continuous-planarity certificate therefore makes their original
source polylines avoid each other, independently of the later direct/fallback
route choice.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 4000000

/-- Original final source routes belonging to different clauses avoid each
other.  This choice-independent form can be reused in every shared-endpoint
terminal-direction argument. -/
theorem retainedFinalCrossClauseSourceRoutes_avoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {firstClause secondClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx)
    (clauseIndicesDifferent :
      firstClauseIndex ≠ secondClauseIndex) :
    RoutesAvoidEachOther
      (finalCoordinatedSourceRoutes
        formula firstClauseIndex firstLiteralIndex)
      (finalCoordinatedSourceRoutes
        formula secondClauseIndex secondLiteralIndex) := by
  let certificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let retainedClausesNonempty :=
    retainedDrawingPlanarSATFormula_clausesNonempty_of_source
      formula sourceClausesNonempty
  let source := finalCoordinatedSource formula
  let placement := finalCoordinatedPlacement formula
  let routes := finalCoordinatedSourceRoutes formula
  let firstRoute := routes firstClauseIndex firstLiteralIndex
  let secondRoute := routes secondClauseIndex secondLiteralIndex
  rcases
      PositionedPeriodicCNF.exists_taggedIncidenceRoute_of_positioned_members
        source placement routes
        firstClauseMember firstLiteralMember with
    ⟨firstRouteIndex, firstIncidenceMember, firstRouteMember⟩
  rcases
      PositionedPeriodicCNF.exists_taggedIncidenceRoute_of_positioned_members
        source placement routes
        secondClauseMember secondLiteralMember with
    ⟨secondRouteIndex, secondIncidenceMember, secondRouteMember⟩
  have routeIndicesDifferent :
      firstRouteIndex ≠ secondRouteIndex := by
    intro indicesEqual
    have taggedEqual :=
      tagged_eq_of_mem_zipIdx_of_snd_eq
        firstIncidenceMember secondIncidenceMember indicesEqual
    exact clauseIndicesDifferent
      (congrArg
        (fun tagged :
            CNFIncidence
                (WrappedPeriodicPlanarSATVariable Variable) × Nat =>
          tagged.1.clauseIndex)
        taggedEqual)
  have firstLength : 2 ≤ firstRoute.length := by
    simpa [firstRoute, routes, source] using
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember firstLiteralMember
  have secondLength : 2 ≤ secondRoute.length := by
    simpa [secondRoute, routes, source] using
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty secondClauseMember secondLiteralMember
  simpa [firstRoute, secondRoute, routes, source] using
    retainedDeduplicatedGaugedWrappedDrawing_routesAvoidEachOther
      formula certificate.graphWellFormed
      certificate.graphDegreeAtMostThree
      certificate.graphIsLocal retainedClausesNonempty
      firstRouteMember secondRouteMember
      firstLength secondLength routeIndicesDifferent

end PeriodicOrthocrossing
end LeanTrominoes
