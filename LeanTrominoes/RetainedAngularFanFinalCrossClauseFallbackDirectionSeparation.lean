import LeanTrominoes.RetainedAngularFanFinalCrossClauseFallbackBoundarySeparation
import LeanTrominoes.RetainedTerminalDirectionEndpointSeparation
import LeanTrominoes.RetainedTerminalDirectionEnumeration

/-!
# Terminal-direction separation for shared-center fallbacks

Failed fallback routes are orthogonal.  At a shared final variable center,
continuous planarity of the retained source therefore forces distinct
classified terminal directions, and hence distinct angular ranks.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 8000000

/-- Failed choices in distinct final source clauses that end at one
canonical variable center have different classified terminal directions. -/
theorem
    retainedFinalCrossClauseFallbackTerminalDirections_ne_of_sameCenter
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
    (firstChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula firstClauseIndex firstLiteralIndex = none)
    (secondChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula secondClauseIndex secondLiteralIndex = none)
    (clauseIndicesDifferent :
      firstClauseIndex ≠ secondClauseIndex)
    (centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          firstClause firstLiteral =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          secondClause secondLiteral) :
    (classifiedRetainedTerminalData
        (routeTerminalVector
          (finalCoordinatedSourceRoutes
            formula firstClauseIndex firstLiteralIndex))).1 ≠
      (classifiedRetainedTerminalData
        (routeTerminalVector
          (finalCoordinatedSourceRoutes
            formula secondClauseIndex secondLiteralIndex))).1 := by
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
  let firstRoute :=
    routes firstClauseIndex firstLiteralIndex
  let secondRoute :=
    routes secondClauseIndex secondLiteralIndex
  let firstTerminal :=
    classifiedRetainedTerminalData
      (routeTerminalVector firstRoute)
  let secondTerminal :=
    classifiedRetainedTerminalData
      (routeTerminalVector secondRoute)
  have copiesDifferent :
      (firstLiteral.atom, firstClauseIndex, firstLiteralIndex) ≠
        (secondLiteral.atom, secondClauseIndex, secondLiteralIndex) := by
    intro copiesEqual
    apply clauseIndicesDifferent
    exact congrArg (fun copy => copy.2.1) copiesEqual
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
    apply copiesDifferent
    have taggedEqual :=
      tagged_eq_of_mem_zipIdx_of_snd_eq
        firstIncidenceMember secondIncidenceMember indicesEqual
    have incidenceEqual := congrArg Prod.fst taggedEqual
    simpa using
      congrArg
        (fun incidence :
            CNFIncidence
              (WrappedPeriodicPlanarSATVariable Variable) =>
          (incidence.literal.atom, incidence.clauseIndex,
            incidence.literalIndex))
        incidenceEqual
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
  have firstOrthogonal :
      OrthogonalPolyline firstRoute := by
    simpa [firstRoute, routes, source] using
      finalCoordinatedFallbackSourceRoute_orthogonal
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        firstClauseMember firstLiteralMember firstChoiceNone
  have secondOrthogonal :
      OrthogonalPolyline secondRoute := by
    simpa [secondRoute, routes, source] using
      finalCoordinatedFallbackSourceRoute_orthogonal
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        secondClauseMember secondLiteralMember secondChoiceNone
  have firstEndpoints :=
    finalCoordinatedSourceRoutes_endpoints
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty firstClauseMember firstLiteralMember
  have secondEndpoints :=
    finalCoordinatedSourceRoutes_endpoints
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty secondClauseMember secondLiteralMember
  have sameFinish :
      firstRoute.getLast? = secondRoute.getLast? := by
    simpa [firstRoute, secondRoute, routes, placement]
      using firstEndpoints.2.trans
        (centersEqual ▸ secondEndpoints.2.symm)
  have sourceRoutesAvoid :
      RoutesAvoidEachOther firstRoute secondRoute :=
    retainedDeduplicatedGaugedWrappedDrawing_routesAvoidEachOther
      formula certificate.graphWellFormed
      certificate.graphDegreeAtMostThree
      certificate.graphIsLocal retainedClausesNonempty
      firstRouteMember secondRouteMember
      firstLength secondLength routeIndicesDifferent
  let firstScaledRoute :=
    scalePolyline retainedAngularFanSourceClearanceFactor
      firstRoute
  let secondScaledRoute :=
    scalePolyline retainedAngularFanSourceClearanceFactor
      secondRoute
  let firstScaledTerminal :=
    scaleRetainedTerminalData
      retainedAngularFanSourceClearanceFactor firstTerminal
  let secondScaledTerminal :=
    scaleRetainedTerminalData
      retainedAngularFanSourceClearanceFactor secondTerminal
  have firstScaledLength : 2 ≤ firstScaledRoute.length := by
    simpa [firstScaledRoute, scalePolyline] using firstLength
  have secondScaledLength : 2 ≤ secondScaledRoute.length := by
    simpa [secondScaledRoute, scalePolyline] using secondLength
  have firstScaledOrthogonal :
      OrthogonalPolyline firstScaledRoute := by
    exact firstOrthogonal.scalePolyline
      retainedAngularFanSourceClearanceFactor_pos
  have secondScaledOrthogonal :
      OrthogonalPolyline secondScaledRoute := by
    exact secondOrthogonal.scalePolyline
      retainedAngularFanSourceClearanceFactor_pos
  have sameScaledFinish :
      firstScaledRoute.getLast? =
        secondScaledRoute.getLast? := by
    simpa [firstScaledRoute, secondScaledRoute, scalePolyline]
      using congrArg
        (Option.map
          (Cell.scale retainedAngularFanSourceClearanceFactor))
        sameFinish
  have scaledRoutesAvoid :
      RoutesAvoidEachOther firstScaledRoute secondScaledRoute := by
    simpa [firstScaledRoute, secondScaledRoute] using
      sourceRoutesAvoid.scalePolyline
        (show
          (0 : Int) <
            retainedAngularFanSourceClearanceFactor by
          exact_mod_cast
            retainedAngularFanSourceClearanceFactor_pos)
  have firstClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector firstScaledRoute) =
        some firstScaledTerminal := by
    simpa [firstScaledRoute, firstScaledTerminal,
      firstRoute, firstTerminal, routes, source] using
      finalCoordinatedScaledSourceRoute_classified
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember firstLiteralMember
  have secondClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector secondScaledRoute) =
        some secondScaledTerminal := by
    simpa [secondScaledRoute, secondScaledTerminal,
      secondRoute, secondTerminal, routes, source] using
      finalCoordinatedScaledSourceRoute_classified
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty secondClauseMember secondLiteralMember
  simpa [firstRoute, secondRoute, firstTerminal, secondTerminal,
    firstScaledTerminal, secondScaledTerminal,
    routes, source] using
    retainedTerminalDirections_ne_of_routesAvoidEachOther
      firstScaledLength secondScaledLength
      firstScaledOrthogonal secondScaledOrthogonal
      sameScaledFinish scaledRoutesAvoid
      firstClassified secondClassified

/-- The preceding direction distinction is equivalent to distinct
east-first angular ranks. -/
theorem
    retainedFinalCrossClauseFallbackTerminalAngularRanks_ne_of_sameCenter
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
    (firstChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula firstClauseIndex firstLiteralIndex = none)
    (secondChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula secondClauseIndex secondLiteralIndex = none)
    (clauseIndicesDifferent :
      firstClauseIndex ≠ secondClauseIndex)
    (centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          firstClause firstLiteral =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          secondClause secondLiteral) :
    (classifiedRetainedTerminalData
        (routeTerminalVector
          (finalCoordinatedSourceRoutes
            formula firstClauseIndex firstLiteralIndex))).1.angularRank ≠
      (classifiedRetainedTerminalData
        (routeTerminalVector
          (finalCoordinatedSourceRoutes
            formula secondClauseIndex secondLiteralIndex))).1.angularRank := by
  intro ranksEqual
  apply
    retainedFinalCrossClauseFallbackTerminalDirections_ne_of_sameCenter
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
      firstClauseMember secondClauseMember
      firstLiteralMember secondLiteralMember
      firstChoiceNone secondChoiceNone clauseIndicesDifferent centersEqual
  exact
    RetainedTerminalDirection.angularRank_injective ranksEqual

end PeriodicOrthocrossing
end LeanTrominoes
