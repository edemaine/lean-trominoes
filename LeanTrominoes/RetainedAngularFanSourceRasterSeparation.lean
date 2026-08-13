/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanSourceMixedSeparation
import LeanTrominoes.RetainedRayRasterizationSeparation
import LeanTrominoes.PositionedPeriodicCNFTaggedRouteLookup

/-!
# Source/fan separation from rasterized route clearance

The mixed angular-fan theorem reduces one directed source-prefix/fan case to
`SourcePrefixCorridorSeparated`.  The retained-ray rasterization lift supplies
that corridor from a finite point/segment and segment/segment rectangle
certificate.

This file specializes the bridge to two genuine routes of the final retained
planar-SAT drawing.  Their flat route memberships recover the clause/literal
metadata needed to obtain the retained-ray certificates automatically.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 2000000

/-- For two genuine final retained source routes, the finite source-polyline
rectangle certificate discharges the directed prefix-versus-complete-fan
separation case after source-first scaling. -/
theorem
    retainedFinalSourceScaledPrefix_strictlyAvoids_otherOuterCompleteRoute_of_sourcePolylineRectanglesSeparated
    {Variable : Type*}
    [variableDecidableEq : DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈
          PeriodicOrthocrossing.retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {factor : Nat} (factorGreaterThanOne : 1 < factor)
    (clearance :
      845 <
        retainedTerminalFanTotalRefinement * factor)
    {firstRoute secondRoute : List Cell}
    {firstIndex secondIndex : Nat}
    {firstSource secondCenter : Cell}
    (firstMember :
      (firstRoute, firstIndex) ∈
        (PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).edgeRoutes.zipIdx)
    (secondMember :
      (secondRoute, secondIndex) ∈
        (PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).edgeRoutes.zipIdx)
    (firstLength : 2 ≤ firstRoute.length)
    (secondLength : 2 ≤ secondRoute.length)
    (indicesDifferent : firstIndex ≠ secondIndex)
    (firstHead : firstRoute.head? = some firstSource)
    (secondLast : secondRoute.getLast? = some secondCenter)
    (sourceNeCenter : firstSource ≠ secondCenter)
    (secondTerminal : RetainedTerminalData)
    (secondSlot : RetainedTerminalSlot)
    (secondClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector secondRoute) =
        some secondTerminal)
    (rectanglesSeparated :
      SourcePolylineRectanglesSeparated
        firstRoute.dropLast secondRoute) :
    RoutesStrictlyAvoidEachOther
      (scalePolyline retainedTerminalFanTotalRefinement
        (scalePolyline factor firstRoute)).dropLast
      (retainedTerminalFanOuterCompleteRoute
        (Cell.scale retainedTerminalFanTotalRefinement
          (Cell.scale factor secondCenter))
        (scaleRetainedTerminalData factor secondTerminal)
        secondSlot) := by
  let source :=
    PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula
  let placement :=
    PeriodicOrthocrossing.retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
      formula
  let routes :=
    PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
      formula
  rcases
      @PositionedPeriodicCNF.exists_incidenceCoordinates_of_taggedRoute
        (PeriodicOrthocrossing.WrappedPeriodicPlanarSATVariable Variable)
        (fun first second =>
          @PeriodicOrthocrossing.instDecidableEqWrappedPeriodicVariable
            (PeriodicOrthocrossing.PeriodicPlanarSATVariable Variable)
            (fun firstOriginal secondOriginal =>
              @PeriodicOrthocrossing.instDecidableEqPeriodicPlanarSATVariable
                Variable variableDecidableEq
                firstOriginal secondOriginal)
            first second)
        source placement routes
        (firstRoute, firstIndex) firstMember with
    ⟨firstIncidence, _firstIncidenceMember,
      firstClause, firstLiteral,
      firstClauseMember, firstLiteralMember,
      firstRouteEq, _firstIndexEq⟩
  rcases
      @PositionedPeriodicCNF.exists_incidenceCoordinates_of_taggedRoute
        (PeriodicOrthocrossing.WrappedPeriodicPlanarSATVariable Variable)
        (fun first second =>
          @PeriodicOrthocrossing.instDecidableEqWrappedPeriodicVariable
            (PeriodicOrthocrossing.PeriodicPlanarSATVariable Variable)
            (fun firstOriginal secondOriginal =>
              @PeriodicOrthocrossing.instDecidableEqPeriodicPlanarSATVariable
                Variable variableDecidableEq
                firstOriginal secondOriginal)
            first second)
        source placement routes
        (secondRoute, secondIndex) secondMember with
    ⟨secondIncidence, _secondIncidenceMember,
      secondClause, secondLiteral,
      secondClauseMember, secondLiteralMember,
      secondRouteEq, _secondIndexEq⟩
  have firstRetained :
      RetainedRayPolyline firstRoute := by
    have firstRouteEq' :
        firstRoute =
          routes firstIncidence.1.clauseIndex
            firstIncidence.1.literalIndex := by
      simpa using firstRouteEq
    have retained :=
      PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_retainedRay
        formula wellFormed degree isLocal clausesNonempty
        (firstClause, firstIncidence.1.clauseIndex)
        firstClauseMember
        (firstLiteral, firstIncidence.1.literalIndex)
        firstLiteralMember
    rw [firstRouteEq']
    simpa [routes] using retained
  have secondRetained :
      RetainedRayPolyline secondRoute := by
    have secondRouteEq' :
        secondRoute =
          routes secondIncidence.1.clauseIndex
            secondIncidence.1.literalIndex := by
      simpa using secondRouteEq
    have retained :=
      PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_retainedRay
        formula wellFormed degree isLocal clausesNonempty
        (secondClause, secondIncidence.1.clauseIndex)
        secondClauseMember
        (secondLiteral, secondIncidence.1.literalIndex)
        secondLiteralMember
    rw [secondRouteEq']
    simpa [routes] using retained
  have corridorSeparated :
      SourcePrefixCorridorSeparated
        firstRoute secondRoute secondTerminal.1 := by
    exact
      sourcePrefixCorridorSeparated_of_sourcePolylineRectanglesSeparated
        firstRoute secondRoute secondTerminal
        firstRetained secondRetained
        firstLength secondLength secondClassified
        rectanglesSeparated
  exact
    retainedFinalSourceScaledPrefix_strictlyAvoids_otherOuterCompleteRoute_of_corridorSeparated
      formula wellFormed degree isLocal clausesNonempty
      factorGreaterThanOne clearance
      firstMember secondMember firstLength secondLength
      indicesDifferent firstHead secondLast sourceNeCenter
      secondTerminal secondSlot secondClassified
      corridorSeparated

end PeriodicEightOccurrenceSplit
end LeanTrominoes
