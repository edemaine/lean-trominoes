/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedFinalFlatRouteShapeClassification

/-!
# Carrier/noncarrier cases for flat final routes

Flat route membership now recovers enough physical metadata to classify the
route without inspecting a segment occurrence.  Every route packages either
as a selected retained carrier lens or as a translated noncarrier macrocell.

Carrier routes also retain the full orthogonality of their finite equality
lens.  Consequently a carrier can never be the oblique fan route in the one
remaining mixed source-prefix/fan orientation.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT
open PeriodicEightOccurrenceSplit

/-- Every genuine flat final route packages either as a carrier occurrence
or as a noncarrier macrocell occurrence. -/
theorem exists_finalGaugedFlatCarrier_or_macrocellWitness
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    (taggedRoute : List Cell × Nat)
    (taggedRouteMember :
      taggedRoute ∈
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).edgeRoutes.zipIdx) :
    Nonempty
        (FinalGaugedFlatCarrierRouteWitness
          formula taggedRoute) ∨
      Nonempty
        (FinalGaugedFlatRouteMacrocellWitness
          formula taggedRoute) := by
  rcases exists_finalGaugedFlatRouteOccurrenceWitness
      formula wellFormed degree isLocal clausesNonempty
      taggedRoute taggedRouteMember with
    ⟨witness⟩
  by_cases carrier :
      ∃ link,
        witness.routeWitness.metadata.source.component =
          .carrier link
  · rcases carrier with ⟨link, componentEq⟩
    exact Or.inl
      (witness.exists_carrierWitness_of_component_eq
        link componentEq)
  · exact Or.inr
      (witness.exists_macrocellWitness_of_not_carrier
        carrier)

/-- A retained metadata source known to be a carrier selects the fully
orthogonal equality-lens drawing. -/
theorem
    DrawingPlanarSATClauseMetadata.retainedLocalDrawingIsOrthogonal_of_carrier
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula)
    (link : EqualityLink CarrierNode)
    (componentEq :
      metadata.source.component = .carrier link) :
    (metadata.source.incidenceDrawing formula).IsOrthogonal := by
  rcases metadata with ⟨clause, source⟩
  cases source <;>
    simp_all [DrawingPlanarSATClauseSource.component,
      DrawingPlanarSATClauseSource.incidenceDrawing]
  exact
    (retainedDrawingPlanarSATCarrierLensIncidenceDrawing_isValid
      wellFormed degree isLocal valid.1).2.1

/-- A flat final carrier occurrence remains fully orthogonal after physical
translation and quotient normalization. -/
theorem
    FinalGaugedFlatCarrierRouteWitness.routeOrthogonal
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {taggedRoute : List Cell × Nat}
    (witness :
      FinalGaugedFlatCarrierRouteWitness
        formula taggedRoute) :
    OrthogonalPolyline taggedRoute.1 := by
  have localDrawingOrthogonal :=
    witness.routeWitness.metadata
      |>.retainedLocalDrawingIsOrthogonal_of_carrier
        wellFormed degree isLocal
        witness.routeWitness.metadata_retainedValid
        witness.link witness.componentEq
  have localClauseMember :=
    witness.routeWitness.metadata.retainedLocalClauseMember
      wellFormed degree isLocal
      witness.routeWitness.metadata_retainedValid
  have localOrthogonal :=
    localDrawingOrthogonal.route_orthogonal_of_members
      localClauseMember witness.routeWitness.literalMember
  have physicalOrthogonal :
      OrthogonalPolyline
        ((retainedDrawingPlanarSATLocalIncidenceDrawing
          formula).routeAt
            (metadataPhysicalIncidence
              witness.routeWitness.metadata
              witness.routeWitness.metadataIndex
              witness.routeWitness.literal
              witness.coordinates.taggedLiteral.2)) := by
    simpa [retainedDrawingPlanarSATLocalIncidenceDrawing_routes,
      retainedDrawingPlanarSATLocalIncidenceRoutes,
      metadataPhysicalIncidence,
      EmbeddedCNFIncidenceDrawing.routeAt,
      witness.routeWitness.metadataLookup] using localOrthogonal
  rw [witness.finalRoute_eq_occurrence,
    witness.routeWitness.routeEq]
  simpa [metadataPhysicalRouteOccurrence, translatePolyline,
    FinalGaugedRouteOccurrenceWitness.physicalShift] using
    physicalOrthogonal.translate
      ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
        formula).translation
        witness.routeWitness.physicalShift)

/-- The discarded final segment of every genuine flat carrier route is
axis-aligned. -/
theorem
    FinalGaugedFlatCarrierRouteWitness.finalSegmentAxisAligned
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {taggedRoute : List Cell × Nat}
    (witness :
      FinalGaugedFlatCarrierRouteWitness
        formula taggedRoute)
    (routeLength : 2 ≤ taggedRoute.1.length)
    {target : Cell}
    (routeLast : taggedRoute.1.getLast? = some target) :
    (⟨polylineLastEntrance taggedRoute.1, target⟩ :
      GridSegment).IsAxisAligned := by
  have orthogonal :=
    witness.routeOrthogonal
      formula wellFormed degree isLocal
  have finalMember :=
    finalGridSegment_mem taggedRoute.1 routeLength
  have aligned :=
    (orthogonalPolyline_iff_segments taggedRoute.1).mp
      orthogonal
      (⟨polylineLastEntrance taggedRoute.1,
        taggedRoute.1.getLastD (0, 0)⟩ : GridSegment)
      finalMember
  have lastD :
      taggedRoute.1.getLastD (0, 0) = target := by
    rw [List.getLastD_eq_getLast?, routeLast, Option.getD_some]
  rw [lastD] at aligned
  exact aligned

end PeriodicOrthocrossing

namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Complete directed source-prefix/fan separation reduces to the single
case where the source is a carrier, the fan route is noncarrier, and their
translated enclosing rectangles overlap.  All other component combinations
are discharged internally. -/
theorem
    retainedFinalSourceScaledPrefix_strictlyAvoids_otherOuterCompleteRoute_of_flatComponentCases
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
          fanSlot))
    (overlapSeparated :
      ∀
        (sourceCarrier :
          PeriodicOrthocrossing.FinalGaugedFlatCarrierRouteWitness
            formula (sourceRoute, sourceIndex))
        (fanMacrocell :
          PeriodicOrthocrossing.FinalGaugedFlatRouteMacrocellWitness
            formula (fanRoute, fanIndex)),
        ¬ClosedGridRectanglesSeparated
            sourceCarrier.rectangleLower sourceCarrier.rectangleUpper
            (PeriodicOrthocrossing.planarSATMacrocellRouteLower
              fanMacrocell.translatedCenter)
            (PeriodicOrthocrossing.planarSATMacrocellRouteUpper
              fanMacrocell.translatedCenter) →
          RoutesStrictlyAvoidEachOther
            (scalePolyline retainedTerminalFanTotalRefinement
              (scalePolyline factor sourceRoute)).dropLast
            (retainedTerminalFanOuterCompleteRoute
              (Cell.scale retainedTerminalFanTotalRefinement
                (Cell.scale factor fanCenter))
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
  rcases
      PeriodicOrthocrossing.exists_finalGaugedFlatCarrier_or_macrocellWitness
        formula wellFormed degree isLocal clausesNonempty
        (sourceRoute, sourceIndex) sourceMember with
    sourceCarrierCase | sourceMacrocellCase
  · rcases sourceCarrierCase with ⟨sourceCarrier⟩
    rcases
        PeriodicOrthocrossing.exists_finalGaugedFlatCarrier_or_macrocellWitness
          formula wellFormed degree isLocal clausesNonempty
          (fanRoute, fanIndex) fanMember with
      fanCarrierCase | fanMacrocellCase
    · rcases fanCarrierCase with ⟨fanCarrier⟩
      have fanAligned :=
        fanCarrier.finalSegmentAxisAligned
          formula wellFormed degree isLocal
          fanLength fanLast
      have separated :=
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
    · rcases fanMacrocellCase with ⟨fanMacrocell⟩
      by_cases rectanglesSeparated :
          ClosedGridRectanglesSeparated
            sourceCarrier.rectangleLower sourceCarrier.rectangleUpper
            (PeriodicOrthocrossing.planarSATMacrocellRouteLower
              fanMacrocell.translatedCenter)
            (PeriodicOrthocrossing.planarSATMacrocellRouteUpper
              fanMacrocell.translatedCenter)
      · exact
          retainedFinalSourceScaledPrefix_strictlyAvoids_otherOuterCompleteRoute_of_flatCarrierMacrocell_rectanglesSeparated
            formula wellFormed degree isLocal clausesNonempty
            factorGreaterThanOne clearance
            sourceMember fanMember sourceLength fanLength
            indicesDifferent sourceHead fanLast sourceNeCenter
            fanTerminal fanSlot fanClassified
            sourceCarrier fanMacrocell rectanglesSeparated
      · exact overlapSeparated
          sourceCarrier fanMacrocell rectanglesSeparated
  · rcases sourceMacrocellCase with ⟨sourceMacrocell⟩
    rcases
        PeriodicOrthocrossing.exists_finalGaugedFlatCarrier_or_macrocellWitness
          formula wellFormed degree isLocal clausesNonempty
          (fanRoute, fanIndex) fanMember with
      fanCarrierCase | fanMacrocellCase
    · rcases fanCarrierCase with ⟨fanCarrier⟩
      have fanAligned :=
        fanCarrier.finalSegmentAxisAligned
          formula wellFormed degree isLocal
          fanLength fanLast
      have separated :=
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
    · rcases fanMacrocellCase with ⟨fanMacrocell⟩
      exact
        retainedFinalSourceScaledPrefix_strictlyAvoids_otherOuterCompleteRoute_of_noncarrierMacrocells
          formula wellFormed degree isLocal clausesNonempty
          factorGreaterThanOne clearance
          sourceMember fanMember sourceLength fanLength
          indicesDifferent headsDifferent sourceHead fanLast
          sourceNeCenter
          sourceTerminal fanTerminal sourceSlot fanSlot
          sourceClassified fanClassified
          sourceMacrocell fanMacrocell fansAvoid

end PeriodicEightOccurrenceSplit
end LeanTrominoes
