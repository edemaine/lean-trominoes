import LeanTrominoes.RetainedFinalFlatRouteComponentCases
import LeanTrominoes.RetainedRayRasterizationSeparation

/-!
# Component cases for oblique final source corridors

An oblique final segment cannot belong to a carrier lens.  Splitting both
flat final routes into carrier and macrocell packages therefore reduces a
source-prefix corridor to two genuinely local configurations: an overlapping
carrier--macrocell pair or two macrocells with the same translated center.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 400000

/-- For an oblique reference route, all flat component combinations produce
the mixed source corridor except the overlapping carrier--macrocell and
equal-macrocell configurations exposed by the two callbacks. -/
theorem
    sourcePrefixCorridorSeparated_of_flatComponentCases_of_referenceFinalSegment_not_axisAligned
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
    (referenceTerminal : RetainedTerminalData)
    (sourceRetained : RetainedRayPolyline sourceRoute)
    (referenceRetained : RetainedRayPolyline referenceRoute)
    (referenceClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector referenceRoute) =
        some referenceTerminal)
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
          SourcePrefixCorridorSeparated
            sourceRoute referenceRoute referenceTerminal.1)
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
          SourcePrefixCorridorSeparated
            sourceRoute referenceRoute referenceTerminal.1) :
    SourcePrefixCorridorSeparated
      sourceRoute referenceRoute referenceTerminal.1 := by
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
          sourcePrefixCorridorSeparated_of_sourcePolylineRectanglesSeparated
            sourceRoute referenceRoute referenceTerminal
            sourceRetained referenceRetained
            sourceLength referenceLength referenceClassified
        exact
          sourcePrefixPolylineRectanglesSeparated_of_flatCarrierMacrocell_rectanglesSeparated
            formula wellFormed degree isLocal
            sourceCarrier referenceMacrocell rectanglesSeparated
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
          sourcePrefixCorridorSeparated_of_sourcePolylineRectanglesSeparated
            sourceRoute referenceRoute referenceTerminal
            sourceRetained referenceRetained
            sourceLength referenceLength referenceClassified
        exact
          sourcePrefixPolylineRectanglesSeparated_of_flatRouteMacrocellCenters_ne
            formula wellFormed degree isLocal
            sourceMacrocell referenceMacrocell centersDifferent
      · exact equalMacrocells
          sourceMacrocell referenceMacrocell
          (not_ne_iff.mp centersDifferent)

end PeriodicOrthocrossing
end LeanTrominoes
