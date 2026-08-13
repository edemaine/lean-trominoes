/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedFinalFlatNormalizedBoundary
import LeanTrominoes.RetainedTerminalBoundaryCheckpointSeparation
import LeanTrominoes.RetainedFinalFlatRouteComponentCases
import LeanTrominoes.RetainedFinalRoutePrefixSeparation

/-!
# Closing normalized carrier--fan corridor separation

The final drawing's ordinary route planarity and simplicity strictly
separate one route's retained prefix from the other complete route.  At the
single overlapping carrier--noncarrier component case, the normalized
carrier boundary turns this strict separation into the exact refined
terminal-checkpoint corridor certificate.

This closes the callback left by the carrier/noncarrier component-case
reducer.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- The retained prefix of one final route is strictly separated from the
other complete route under the same endpoint hypotheses used by the final
source splice. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_routePrefix_strictlyAvoids_otherRoute
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {first second : List Cell}
    {firstIndex secondIndex : Nat}
    {firstSource secondFinal : Cell}
    (firstMember :
      (first, firstIndex) ∈
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).edgeRoutes.zipIdx)
    (secondMember :
      (second, secondIndex) ∈
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).edgeRoutes.zipIdx)
    (firstLength : 2 ≤ first.length)
    (secondLength : 2 ≤ second.length)
    (indicesDifferent : firstIndex ≠ secondIndex)
    (headsDifferent : first.head? ≠ second.head?)
    (firstHead : first.head? = some firstSource)
    (secondLast : second.getLast? = some secondFinal)
    (sourceNeFinal : firstSource ≠ secondFinal) :
    RoutesStrictlyAvoidEachOther first.dropLast second := by
  have prefixesAvoid :=
    retainedDeduplicatedGaugedWrappedDrawing_routePrefixes_strictlyAvoid
      formula wellFormed degree isLocal clausesNonempty
      firstMember secondMember firstLength secondLength
      indicesDifferent headsDifferent
  have finalSegmentAvoid :=
    retainedDeduplicatedGaugedWrappedDrawing_routePrefix_strictlyAvoids_otherFinalSegment
      formula wellFormed degree isLocal clausesNonempty
      firstMember secondMember firstLength secondLength
      indicesDifferent headsDifferent firstHead secondLast sourceNeFinal
  have reverseTailExists :=
    exists_reverse_tail_head?_of_two_le_length
      second secondLength
  have entranceEq :
      second.dropLast.getLast? =
        some (polylineLastEntrance second) :=
    dropLast_getLast?_of_reverse_tail_head?
      (polylineLastEntrance_spec reverseTailExists)
  have joined :=
    prefixesAvoid.join_right
      finalSegmentAvoid entranceEq (by simp)
  have decomposition :
      second.dropLast ++ [secondFinal] = second :=
    List.dropLast_append_getLast?
      secondFinal secondLast
  simpa [joinAtEndpoint, decomposition] using joined

/-- An overlapping flat carrier prefix and oblique macrocell route have the
exact mixed source-corridor certificate.  The normalized contact determines
a carrier boundary with the prefix outside and the macrocell route inside;
ordinary route planarity then excludes every boundary checkpoint. -/
theorem
    sourcePrefixCorridorSeparated_of_flatCarrierMacrocell_rectangles_not_separated
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {sourceRoute referenceRoute : List Cell}
    {sourceIndex referenceIndex : Nat}
    {sourcePoint referenceTarget : Cell}
    (sourceMember :
      (sourceRoute, sourceIndex) ∈
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).edgeRoutes.zipIdx)
    (referenceMember :
      (referenceRoute, referenceIndex) ∈
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).edgeRoutes.zipIdx)
    (sourceLength : 2 ≤ sourceRoute.length)
    (referenceLength : 2 ≤ referenceRoute.length)
    (indicesDifferent : sourceIndex ≠ referenceIndex)
    (headsDifferent : sourceRoute.head? ≠ referenceRoute.head?)
    (sourceHead : sourceRoute.head? = some sourcePoint)
    (referenceLast :
      referenceRoute.getLast? = some referenceTarget)
    (sourceNeTarget : sourcePoint ≠ referenceTarget)
    (referenceTerminal : RetainedTerminalData)
    (referenceClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector referenceRoute) =
        some referenceTerminal)
    (sourceCarrier :
      FinalGaugedFlatCarrierRouteWitness
        formula (sourceRoute, sourceIndex))
    (referenceMacrocell :
      FinalGaugedFlatRouteMacrocellWitness
        formula (referenceRoute, referenceIndex))
    (referenceOblique :
      ¬(⟨polylineLastEntrance referenceRoute,
          referenceTarget⟩ : GridSegment).IsAxisAligned)
    (rectanglesNotSeparated :
      ¬ClosedGridRectanglesSeparated
        sourceCarrier.rectangleLower sourceCarrier.rectangleUpper
        (planarSATMacrocellRouteLower
          referenceMacrocell.translatedCenter)
        (planarSATMacrocellRouteUpper
          referenceMacrocell.translatedCenter)) :
    SourcePrefixCorridorSeparated
      sourceRoute referenceRoute referenceTerminal.1 := by
  rcases
      referenceMacrocell.exists_normalizedSource
        formula wellFormed degree isLocal with
    ⟨normalized⟩
  have contact :=
    sourceCarrier.normalizedContact_of_finalSegment_not_axisAligned
      formula wellFormed degree isLocal
      referenceMacrocell normalized
      referenceLength referenceLast referenceOblique
      rectanglesNotSeparated
  rcases
      sourceCarrier.exists_normalizedCarrierBoundary
        formula wellFormed degree isLocal
        referenceMacrocell normalized contact with
    ⟨boundary⟩
  have strictlyAvoid :=
    retainedDeduplicatedGaugedWrappedDrawing_routePrefix_strictlyAvoids_otherRoute
      formula wellFormed degree isLocal clausesNonempty
      sourceMember referenceMember sourceLength referenceLength
      indicesDifferent headsDifferent sourceHead referenceLast
      sourceNeTarget
  apply
    sourcePrefixCorridorSeparated_of_outside_insideCarrierBoundary
      boundary.port boundary.origin
      sourceRoute referenceRoute referenceTerminal
      referenceLength referenceClassified
  · intro point pointMember
    exact boundary.carrierOutside point
      (List.mem_of_mem_dropLast pointMember)
  · exact boundary.macrocellInside
  · exact strictlyAvoid

end PeriodicOrthocrossing

namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 1600000

/-- All component combinations of the final directed source-prefix versus
other-fan cross case are strictly separated.  In the last overlapping
carrier--oblique-fan case, normalized carrier-boundary checkpoint separation
supplies the mixed corridor certificate. -/
theorem
    retainedFinalSourceScaledPrefix_strictlyAvoids_otherOuterCompleteRoute
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
          (Cell.scale factor fanCenter))
        (scaleRetainedTerminalData factor fanTerminal)
        fanSlot) := by
  apply
    retainedFinalSourceScaledPrefix_strictlyAvoids_otherOuterCompleteRoute_of_flatComponentCases
      formula wellFormed degree isLocal clausesNonempty
      factorGreaterThanOne clearance
      sourceMember fanMember sourceLength fanLength
      indicesDifferent headsDifferent sourceHead fanLast
      sourceNeCenter
      sourceTerminal fanTerminal sourceSlot fanSlot
      sourceClassified fanClassified fansAvoid
  intro sourceCarrier fanMacrocell rectanglesNotSeparated
  by_cases fanAligned :
      (⟨polylineLastEntrance fanRoute, fanCenter⟩ :
        GridSegment).IsAxisAligned
  · have separated :=
      retainedFinalSourceScaledPrefix_strictlyAvoids_otherOuterCompleteRoute_of_singleton_or_axisAligned
        formula wellFormed degree isLocal clausesNonempty
        factorGreaterThanOne
        sourceMember fanMember sourceLength fanLength
        indicesDifferent headsDifferent sourceHead fanLast
        sourceNeCenter
        sourceTerminal fanTerminal sourceSlot fanSlot
        sourceClassified fanClassified
        (Or.inr fanAligned) fansAvoid
    have fanLastD :
        fanRoute.getLastD (0, 0) = fanCenter := by
      simp [List.getLastD_eq_getLast?, fanLast]
    rw [scalePolyline_getLastD, fanLastD] at separated
    exact separated
  · have corridor :=
      PeriodicOrthocrossing.sourcePrefixCorridorSeparated_of_flatCarrierMacrocell_rectangles_not_separated
        formula wellFormed degree isLocal clausesNonempty
        sourceMember fanMember sourceLength fanLength
        indicesDifferent headsDifferent sourceHead fanLast
        sourceNeCenter fanTerminal fanClassified
        sourceCarrier fanMacrocell fanAligned rectanglesNotSeparated
    exact
      retainedFinalSourceScaledPrefix_strictlyAvoids_otherOuterCompleteRoute_of_corridorSeparated
        formula wellFormed degree isLocal clausesNonempty
        factorGreaterThanOne clearance
        sourceMember fanMember sourceLength fanLength
        indicesDifferent sourceHead fanLast sourceNeCenter
        fanTerminal fanSlot fanClassified corridor

/-- Once the two complete outer fans are separated, the unconditional
directed source-prefix/fan theorem closes both cross orientations and hence
separates the two complete source-to-boundary splices. -/
theorem
    retainedFinalSourceScaledSplicedBoundaryPolylines_strictlyAvoid
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
    retainedFinalSourceScaledPrefix_strictlyAvoids_otherOuterCompleteRoute
      formula wellFormed degree isLocal clausesNonempty
      factorGreaterThanOne clearance
      firstMember secondMember firstLength secondLength
      indicesDifferent headsDifferent firstHead secondLast
      firstSourceNeSecondCenter
      firstTerminal secondTerminal firstSlot secondSlot
      firstClassified secondClassified fansAvoid
  have secondPrefixAvoidFirstFan :=
    retainedFinalSourceScaledPrefix_strictlyAvoids_otherOuterCompleteRoute
      formula wellFormed degree isLocal clausesNonempty
      factorGreaterThanOne clearance
      secondMember firstMember secondLength firstLength
      (Ne.symm indicesDifferent) (Ne.symm headsDifferent)
      secondHead firstLast secondSourceNeFirstCenter
      secondTerminal firstTerminal secondSlot firstSlot
      secondClassified firstClassified fansAvoid.symm
  have firstLastD :
      firstRoute.getLastD (0, 0) = firstCenter := by
    simp [List.getLastD_eq_getLast?, firstLast]
  have secondLastD :
      secondRoute.getLastD (0, 0) = secondCenter := by
    simp [List.getLastD_eq_getLast?, secondLast]
  have firstPrefixAvoidSecondFan' :
      RoutesStrictlyAvoidEachOther
        (scalePolyline retainedTerminalFanTotalRefinement
          (scalePolyline factor firstRoute)).dropLast
        (retainedTerminalFanOuterCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            ((scalePolyline factor secondRoute).getLastD (0, 0)))
          (scaleRetainedTerminalData factor secondTerminal)
          secondSlot) := by
    rw [scalePolyline_getLastD, secondLastD]
    exact firstPrefixAvoidSecondFan
  have secondPrefixAvoidFirstFan' :
      RoutesStrictlyAvoidEachOther
        (scalePolyline retainedTerminalFanTotalRefinement
          (scalePolyline factor secondRoute)).dropLast
        (retainedTerminalFanOuterCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            ((scalePolyline factor firstRoute).getLastD (0, 0)))
          (scaleRetainedTerminalData factor firstTerminal)
          firstSlot) := by
    rw [scalePolyline_getLastD, firstLastD]
    exact secondPrefixAvoidFirstFan
  exact
    retainedAngularFanSourceScaledSplicedBoundaryPolylines_strictlyAvoid
      (by omega)
      firstRoute secondRoute firstTerminal secondTerminal
      firstSlot secondSlot firstLength secondLength
      firstClassified secondClassified sourcePrefixesAvoid
      firstPrefixAvoidSecondFan'
      secondPrefixAvoidFirstFan'.symm
      fansAvoid

end PeriodicEightOccurrenceSplit
end LeanTrominoes
