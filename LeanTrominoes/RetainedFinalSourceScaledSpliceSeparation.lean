import LeanTrominoes.RetainedAngularFanSourceRadialSeparation
import LeanTrominoes.RetainedAngularFanSourceScaledSeparation

/-!
# Final retained source-splice separation by route shape

For one directed source-prefix/fan cross case, two certificates already
cover the useful route-shape alternatives.  A singleton source prefix is
just its own fan gate, so fan/fan separation suffices.  If the other route's
discarded terminal is axis-aligned, inherited source-route separation clears
its complete fan directly.

This module packages that dichotomy and then applies it in both directions.
Thus two final retained source splices are strictly separated whenever each
directed cross has one of those two witnesses.  In particular, pairs with
two aligned terminals and pairs with two singleton prefixes are complete;
only the genuinely mixed aligned-prefix/oblique-fan direction remains for
the global drawing.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 2000000

/-- A directed final source-prefix/fan cross is discharged either by a
singleton source prefix or by an axis-aligned terminal on the fan route. -/
theorem
    retainedFinalSourceScaledPrefix_strictlyAvoids_otherOuterCompleteRoute_of_singleton_or_axisAligned
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
    {sourceRoute fanRoute : List Cell}
    {sourceIndex fanIndex : Nat}
    {sourcePoint fanCenter : Cell}
    (sourceMember :
      (sourceRoute, sourceIndex) ∈
        (PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).edgeRoutes.zipIdx)
    (fanMember :
      (fanRoute, fanIndex) ∈
        (PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).edgeRoutes.zipIdx)
    (sourceLength : 2 ≤ sourceRoute.length)
    (fanLength : 2 ≤ fanRoute.length)
    (indicesDifferent : sourceIndex ≠ fanIndex)
    (headsDifferent : sourceRoute.head? ≠ fanRoute.head?)
    (sourceHead : sourceRoute.head? = some sourcePoint)
    (fanLast : fanRoute.getLast? = some fanCenter)
    (sourceNeCenter : sourcePoint ≠ fanCenter)
    (sourceTerminal fanTerminal : RetainedTerminalData)
    (sourceSlot fanSlot : RetainedTerminalSlot)
    (sourceClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector sourceRoute) =
        some sourceTerminal)
    (fanClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector fanRoute) =
        some fanTerminal)
    (shape :
      sourceRoute.dropLast.length = 1 ∨
        (⟨polylineLastEntrance fanRoute, fanCenter⟩ :
          GridSegment).IsAxisAligned)
    (fansAvoid :
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanOuterCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            ((scalePolyline factor sourceRoute).getLastD (0, 0)))
          (scaleRetainedTerminalData factor sourceTerminal)
          sourceSlot)
        (retainedTerminalFanOuterCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            ((scalePolyline factor fanRoute).getLastD (0, 0)))
          (scaleRetainedTerminalData factor fanTerminal)
          fanSlot)) :
    RoutesStrictlyAvoidEachOther
      (scalePolyline retainedTerminalFanTotalRefinement
        (scalePolyline factor sourceRoute)).dropLast
      (retainedTerminalFanOuterCompleteRoute
        (Cell.scale retainedTerminalFanTotalRefinement
          ((scalePolyline factor fanRoute).getLastD (0, 0)))
        (scaleRetainedTerminalData factor fanTerminal)
        fanSlot) := by
  rcases shape with singletonPrefix | fanAligned
  · exact
      retainedAngularFanSourceScaledPrefix_strictlyAvoids_otherOuterCompleteRoute_of_singletonPrefix
        (Nat.zero_lt_of_lt factorGreaterThanOne)
        sourceRoute sourceTerminal
        (scaleRetainedTerminalData factor fanTerminal)
        sourceSlot fanSlot
        (Cell.scale retainedTerminalFanTotalRefinement
          ((scalePolyline factor fanRoute).getLastD (0, 0)))
        sourceLength sourceClassified singletonPrefix fansAvoid
  · have separated :=
      retainedFinalSourceScaledPrefix_strictlyAvoids_otherOuterCompleteRoute_of_axisAligned
        formula wellFormed degree isLocal clausesNonempty
        factorGreaterThanOne
        sourceMember fanMember sourceLength fanLength
        indicesDifferent headsDifferent sourceHead fanLast
        sourceNeCenter fanTerminal fanSlot fanClassified fanAligned
    have fanLastD :
        fanRoute.getLastD (0, 0) = fanCenter := by
      simp [List.getLastD_eq_getLast?, fanLast]
    rw [scalePolyline_getLastD, fanLastD]
    simpa using separated

/-- Two final retained source-to-boundary splices are strictly separated
once the singleton-or-aligned dichotomy is available in both directed
cross orientations. -/
theorem
    retainedFinalSourceScaledSplicedBoundaryPolylines_strictlyAvoid_of_shapes
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
    {firstRoute secondRoute : List Cell}
    {firstIndex secondIndex : Nat}
    {firstSource secondSource firstCenter secondCenter : Cell}
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
    (headsDifferent : firstRoute.head? ≠ secondRoute.head?)
    (firstHead : firstRoute.head? = some firstSource)
    (secondHead : secondRoute.head? = some secondSource)
    (firstLast : firstRoute.getLast? = some firstCenter)
    (secondLast : secondRoute.getLast? = some secondCenter)
    (firstSourceNeSecondCenter : firstSource ≠ secondCenter)
    (secondSourceNeFirstCenter : secondSource ≠ firstCenter)
    (firstTerminal secondTerminal : RetainedTerminalData)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (firstClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector firstRoute) =
        some firstTerminal)
    (secondClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector secondRoute) =
        some secondTerminal)
    (firstShape :
      firstRoute.dropLast.length = 1 ∨
        (⟨polylineLastEntrance secondRoute, secondCenter⟩ :
          GridSegment).IsAxisAligned)
    (secondShape :
      secondRoute.dropLast.length = 1 ∨
        (⟨polylineLastEntrance firstRoute, firstCenter⟩ :
          GridSegment).IsAxisAligned)
    (fansAvoid :
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanOuterCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            ((scalePolyline factor firstRoute).getLastD (0, 0)))
          (scaleRetainedTerminalData factor firstTerminal)
          firstSlot)
        (retainedTerminalFanOuterCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            ((scalePolyline factor secondRoute).getLastD (0, 0)))
          (scaleRetainedTerminalData factor secondTerminal)
          secondSlot)) :
    RoutesStrictlyAvoidEachOther
      (retainedAngularFanSplicedBoundaryPolyline
        (scalePolyline factor firstRoute)
        (scaleRetainedTerminalData factor firstTerminal)
        firstSlot)
      (retainedAngularFanSplicedBoundaryPolyline
        (scalePolyline factor secondRoute)
        (scaleRetainedTerminalData factor secondTerminal)
        secondSlot) := by
  have sourcePrefixesAvoid :
      RoutesStrictlyAvoidEachOther
        firstRoute.dropLast secondRoute.dropLast :=
    PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawing_routePrefixes_strictlyAvoid
      formula wellFormed degree isLocal clausesNonempty
      firstMember secondMember firstLength secondLength
      indicesDifferent headsDifferent
  have firstPrefixAvoidSecondFan :=
    retainedFinalSourceScaledPrefix_strictlyAvoids_otherOuterCompleteRoute_of_singleton_or_axisAligned
      formula wellFormed degree isLocal clausesNonempty
      factorGreaterThanOne
      firstMember secondMember firstLength secondLength
      indicesDifferent headsDifferent firstHead secondLast
      firstSourceNeSecondCenter
      firstTerminal secondTerminal firstSlot secondSlot
      firstClassified secondClassified firstShape fansAvoid
  have secondPrefixAvoidFirstFan :=
    retainedFinalSourceScaledPrefix_strictlyAvoids_otherOuterCompleteRoute_of_singleton_or_axisAligned
      formula wellFormed degree isLocal clausesNonempty
      factorGreaterThanOne
      secondMember firstMember secondLength firstLength
      (Ne.symm indicesDifferent) (Ne.symm headsDifferent)
      secondHead firstLast secondSourceNeFirstCenter
      secondTerminal firstTerminal secondSlot firstSlot
      secondClassified firstClassified secondShape fansAvoid.symm
  exact
    retainedAngularFanSourceScaledSplicedBoundaryPolylines_strictlyAvoid
      (by omega)
      firstRoute secondRoute firstTerminal secondTerminal
      firstSlot secondSlot firstLength secondLength
      firstClassified secondClassified sourcePrefixesAvoid
      firstPrefixAvoidSecondFan
      secondPrefixAvoidFirstFan.symm
      fansAvoid

/-- The route-shape reducer immediately closes a pair whose two discarded
terminals are axis-aligned. -/
theorem
    retainedFinalSourceScaledSplicedBoundaryPolylines_strictlyAvoid_of_axisAligned
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
    {firstRoute secondRoute : List Cell}
    {firstIndex secondIndex : Nat}
    {firstSource secondSource firstCenter secondCenter : Cell}
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
    (headsDifferent : firstRoute.head? ≠ secondRoute.head?)
    (firstHead : firstRoute.head? = some firstSource)
    (secondHead : secondRoute.head? = some secondSource)
    (firstLast : firstRoute.getLast? = some firstCenter)
    (secondLast : secondRoute.getLast? = some secondCenter)
    (firstSourceNeSecondCenter : firstSource ≠ secondCenter)
    (secondSourceNeFirstCenter : secondSource ≠ firstCenter)
    (firstTerminal secondTerminal : RetainedTerminalData)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (firstClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector firstRoute) =
        some firstTerminal)
    (secondClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector secondRoute) =
        some secondTerminal)
    (firstAligned :
      (⟨polylineLastEntrance firstRoute, firstCenter⟩ :
        GridSegment).IsAxisAligned)
    (secondAligned :
      (⟨polylineLastEntrance secondRoute, secondCenter⟩ :
        GridSegment).IsAxisAligned)
    (fansAvoid :
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanOuterCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            ((scalePolyline factor firstRoute).getLastD (0, 0)))
          (scaleRetainedTerminalData factor firstTerminal)
          firstSlot)
        (retainedTerminalFanOuterCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            ((scalePolyline factor secondRoute).getLastD (0, 0)))
          (scaleRetainedTerminalData factor secondTerminal)
          secondSlot)) :
    RoutesStrictlyAvoidEachOther
      (retainedAngularFanSplicedBoundaryPolyline
        (scalePolyline factor firstRoute)
        (scaleRetainedTerminalData factor firstTerminal)
        firstSlot)
      (retainedAngularFanSplicedBoundaryPolyline
        (scalePolyline factor secondRoute)
        (scaleRetainedTerminalData factor secondTerminal)
        secondSlot) :=
  retainedFinalSourceScaledSplicedBoundaryPolylines_strictlyAvoid_of_shapes
    formula wellFormed degree isLocal clausesNonempty
    factorGreaterThanOne
    firstMember secondMember firstLength secondLength
    indicesDifferent headsDifferent
    firstHead secondHead firstLast secondLast
    firstSourceNeSecondCenter secondSourceNeFirstCenter
    firstTerminal secondTerminal firstSlot secondSlot
    firstClassified secondClassified
    (Or.inr secondAligned) (Or.inr firstAligned) fansAvoid

/-- The route-shape reducer also closes a pair whose two source prefixes
are singletons. -/
theorem
    retainedFinalSourceScaledSplicedBoundaryPolylines_strictlyAvoid_of_singletonPrefixes
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
    {firstRoute secondRoute : List Cell}
    {firstIndex secondIndex : Nat}
    {firstSource secondSource firstCenter secondCenter : Cell}
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
    (headsDifferent : firstRoute.head? ≠ secondRoute.head?)
    (firstHead : firstRoute.head? = some firstSource)
    (secondHead : secondRoute.head? = some secondSource)
    (firstLast : firstRoute.getLast? = some firstCenter)
    (secondLast : secondRoute.getLast? = some secondCenter)
    (firstSourceNeSecondCenter : firstSource ≠ secondCenter)
    (secondSourceNeFirstCenter : secondSource ≠ firstCenter)
    (firstTerminal secondTerminal : RetainedTerminalData)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (firstClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector firstRoute) =
        some firstTerminal)
    (secondClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector secondRoute) =
        some secondTerminal)
    (firstSingleton : firstRoute.dropLast.length = 1)
    (secondSingleton : secondRoute.dropLast.length = 1)
    (fansAvoid :
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanOuterCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            ((scalePolyline factor firstRoute).getLastD (0, 0)))
          (scaleRetainedTerminalData factor firstTerminal)
          firstSlot)
        (retainedTerminalFanOuterCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            ((scalePolyline factor secondRoute).getLastD (0, 0)))
          (scaleRetainedTerminalData factor secondTerminal)
          secondSlot)) :
    RoutesStrictlyAvoidEachOther
      (retainedAngularFanSplicedBoundaryPolyline
        (scalePolyline factor firstRoute)
        (scaleRetainedTerminalData factor firstTerminal)
        firstSlot)
      (retainedAngularFanSplicedBoundaryPolyline
        (scalePolyline factor secondRoute)
        (scaleRetainedTerminalData factor secondTerminal)
        secondSlot) :=
  retainedFinalSourceScaledSplicedBoundaryPolylines_strictlyAvoid_of_shapes
    formula wellFormed degree isLocal clausesNonempty
    factorGreaterThanOne
    firstMember secondMember firstLength secondLength
    indicesDifferent headsDifferent
    firstHead secondHead firstLast secondLast
    firstSourceNeSecondCenter secondSourceNeFirstCenter
    firstTerminal secondTerminal firstSlot secondSlot
    firstClassified secondClassified
    (Or.inl firstSingleton) (Or.inl secondSingleton) fansAvoid

end PeriodicEightOccurrenceSplit
end LeanTrominoes
