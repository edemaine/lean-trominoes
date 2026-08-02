import LeanTrominoes.RetainedFinalFlatRouteComponentCases
import LeanTrominoes.PolylineBoundingBoxRasterSeparation

/-!
# Flat-component cases for final-segment rectangles

An oblique final segment cannot belong to a carrier lens.  Decomposing it
and another flat route into carrier or macrocell witnesses therefore reduces
separation of their endpoint rectangles to an overlapping carrier--macrocell
pair or two macrocells with the same translated center.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 400000

/-- For an oblique reference route, separated component boxes separate the
two final-segment endpoint rectangles.  Only an overlapping source carrier
and equal translated macrocells are delegated to callbacks. -/
theorem
    finalSegmentRectanglesSeparated_of_flatComponentCases_of_referenceFinalSegment_not_axisAligned
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
    {referenceTarget : Cell}
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
    (referenceLast :
      referenceRoute.getLast? = some referenceTarget)
    (referenceOblique :
      ¬(⟨polylineLastEntrance referenceRoute,
          referenceTarget⟩ : GridSegment).IsAxisAligned)
    (carrierOverlap :
      ∀
        (sourceCarrier :
          FinalGaugedFlatCarrierRouteWitness
            formula (sourceRoute, sourceIndex))
        (referenceMacrocell :
          FinalGaugedFlatRouteMacrocellWitness
            formula (referenceRoute, referenceIndex)),
        ¬ClosedGridRectanglesSeparated
            sourceCarrier.rectangleLower sourceCarrier.rectangleUpper
            (planarSATMacrocellRouteLower
              referenceMacrocell.translatedCenter)
            (planarSATMacrocellRouteUpper
              referenceMacrocell.translatedCenter) →
          ClosedGridRectanglesSeparated
            (⟨polylineLastEntrance sourceRoute,
                sourceRoute.getLastD (0, 0)⟩ : GridSegment).coordinateLower
            (⟨polylineLastEntrance sourceRoute,
                sourceRoute.getLastD (0, 0)⟩ : GridSegment).coordinateUpper
            (⟨polylineLastEntrance referenceRoute,
                referenceRoute.getLastD (0, 0)⟩ : GridSegment).coordinateLower
            (⟨polylineLastEntrance referenceRoute,
                referenceRoute.getLastD (0, 0)⟩ : GridSegment).coordinateUpper)
    (equalMacrocells :
      ∀
        (sourceMacrocell :
          FinalGaugedFlatRouteMacrocellWitness
            formula (sourceRoute, sourceIndex))
        (referenceMacrocell :
          FinalGaugedFlatRouteMacrocellWitness
            formula (referenceRoute, referenceIndex)),
        sourceMacrocell.translatedCenter =
            referenceMacrocell.translatedCenter →
          ClosedGridRectanglesSeparated
            (⟨polylineLastEntrance sourceRoute,
                sourceRoute.getLastD (0, 0)⟩ : GridSegment).coordinateLower
            (⟨polylineLastEntrance sourceRoute,
                sourceRoute.getLastD (0, 0)⟩ : GridSegment).coordinateUpper
            (⟨polylineLastEntrance referenceRoute,
                referenceRoute.getLastD (0, 0)⟩ : GridSegment).coordinateLower
            (⟨polylineLastEntrance referenceRoute,
                referenceRoute.getLastD (0, 0)⟩ : GridSegment).coordinateUpper) :
    ClosedGridRectanglesSeparated
      (⟨polylineLastEntrance sourceRoute,
          sourceRoute.getLastD (0, 0)⟩ : GridSegment).coordinateLower
      (⟨polylineLastEntrance sourceRoute,
          sourceRoute.getLastD (0, 0)⟩ : GridSegment).coordinateUpper
      (⟨polylineLastEntrance referenceRoute,
          referenceRoute.getLastD (0, 0)⟩ : GridSegment).coordinateLower
      (⟨polylineLastEntrance referenceRoute,
          referenceRoute.getLastD (0, 0)⟩ : GridSegment).coordinateUpper := by
  let sourceFinal : GridSegment :=
    ⟨polylineLastEntrance sourceRoute,
      sourceRoute.getLastD (0, 0)⟩
  let referenceFinal : GridSegment :=
    ⟨polylineLastEntrance referenceRoute,
      referenceRoute.getLastD (0, 0)⟩
  have sourceFinalMember :
      sourceFinal ∈ gridPolylineSegments sourceRoute := by
    exact finalGridSegment_mem sourceRoute sourceLength
  have referenceFinalMember :
      referenceFinal ∈ gridPolylineSegments referenceRoute := by
    exact finalGridSegment_mem referenceRoute referenceLength
  have sourceFinalEndpoints :=
    gridPolylineSegments_endpoints_mem sourceFinalMember
  have referenceFinalEndpoints :=
    gridPolylineSegments_endpoints_mem referenceFinalMember
  rcases
      exists_finalGaugedFlatCarrier_or_macrocellWitness
        formula wellFormed degree isLocal clausesNonempty
        (sourceRoute, sourceIndex) sourceMember with
    sourceCarrierCase | sourceMacrocellCase
  · rcases sourceCarrierCase with ⟨sourceCarrier⟩
    rcases
        exists_finalGaugedFlatCarrier_or_macrocellWitness
          formula wellFormed degree isLocal clausesNonempty
          (referenceRoute, referenceIndex) referenceMember with
      referenceCarrierCase | referenceMacrocellCase
    · rcases referenceCarrierCase with ⟨referenceCarrier⟩
      exact (referenceOblique
        (referenceCarrier.finalSegmentAxisAligned
          formula wellFormed degree isLocal
          referenceLength referenceLast)).elim
    · rcases referenceMacrocellCase with ⟨referenceMacrocell⟩
      by_cases rectanglesSeparated :
          ClosedGridRectanglesSeparated
            sourceCarrier.rectangleLower sourceCarrier.rectangleUpper
            (planarSATMacrocellRouteLower
              referenceMacrocell.translatedCenter)
            (planarSATMacrocellRouteUpper
              referenceMacrocell.translatedCenter)
      · apply
          PeriodicEightOccurrenceSplit.GridSegment.coordinateRectanglesSeparated_of_inClosedGridRectangles
            (first := sourceFinal) (second := referenceFinal)
        · exact sourceCarrier.routePoints_in_rectangle
            formula wellFormed degree isLocal sourceFinalEndpoints.1
        · exact sourceCarrier.routePoints_in_rectangle
            formula wellFormed degree isLocal sourceFinalEndpoints.2
        · exact referenceMacrocell.routePoints_in_translatedMacrocell
            formula wellFormed degree isLocal referenceFinalEndpoints.1
        · exact referenceMacrocell.routePoints_in_translatedMacrocell
            formula wellFormed degree isLocal referenceFinalEndpoints.2
        · exact rectanglesSeparated
      · exact carrierOverlap
          sourceCarrier referenceMacrocell rectanglesSeparated
  · rcases sourceMacrocellCase with ⟨sourceMacrocell⟩
    rcases
        exists_finalGaugedFlatCarrier_or_macrocellWitness
          formula wellFormed degree isLocal clausesNonempty
          (referenceRoute, referenceIndex) referenceMember with
      referenceCarrierCase | referenceMacrocellCase
    · rcases referenceCarrierCase with ⟨referenceCarrier⟩
      exact (referenceOblique
        (referenceCarrier.finalSegmentAxisAligned
          formula wellFormed degree isLocal
          referenceLength referenceLast)).elim
    · rcases referenceMacrocellCase with ⟨referenceMacrocell⟩
      by_cases centersDifferent :
          sourceMacrocell.translatedCenter ≠
            referenceMacrocell.translatedCenter
      · apply
          PeriodicEightOccurrenceSplit.GridSegment.coordinateRectanglesSeparated_of_inClosedGridRectangles
            (first := sourceFinal) (second := referenceFinal)
        · exact sourceMacrocell.routePoints_in_translatedMacrocell
            formula wellFormed degree isLocal sourceFinalEndpoints.1
        · exact sourceMacrocell.routePoints_in_translatedMacrocell
            formula wellFormed degree isLocal sourceFinalEndpoints.2
        · exact referenceMacrocell.routePoints_in_translatedMacrocell
            formula wellFormed degree isLocal referenceFinalEndpoints.1
        · exact referenceMacrocell.routePoints_in_translatedMacrocell
            formula wellFormed degree isLocal referenceFinalEndpoints.2
        · exact planarSATMacrocellRouteRectangles_separated
            centersDifferent
      · exact equalMacrocells
          sourceMacrocell referenceMacrocell
          (not_ne_iff.mp centersDifferent)

end PeriodicOrthocrossing
end LeanTrominoes
