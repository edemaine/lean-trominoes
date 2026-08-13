/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedNoncarrierSegmentBounds
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedRouteBounds

/-!
# Translation bounds for final gauged segment contacts

All final routes lie in the expanded one-cell halo.  The stronger half-open
bound for noncarrier segments reduces any contact involving a noncarrier to
one of the nine neighboring relative translations.  Only carrier--carrier
contacts can require the full 25-shift expanded-square analysis.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Pointwise final route bounds imply the expanded endpoint bounds used by
continuous segment-contact normalization. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_segmentEndpointsInExpandedSquare
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ []) :
    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
      formula).SegmentEndpointsInExpandedSquare :=
  PeriodicGridDrawing.segmentEndpointsInExpandedSquare_of_routePoints
    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_routePointsInExpandedSquare
      formula wellFormed degree isLocal clausesNonempty)

/-- Every hypothetical final continuous segment contact has one of the 25
relative translations in the doubled neighboring block. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_relativeTranslate_mem_doubleNeighbor_of_interiorsMeet
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {firstIndexed secondIndexed : IndexedGridSegment}
    (firstMember :
      firstIndexed ∈
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).indexedSegments)
    (secondMember :
      secondIndexed ∈
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).indexedSegments)
    {firstShift secondShift : Cell}
    (meet :
      GridSegment.InteriorsMeet
        (firstIndexed.segment.translate
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation firstShift))
        (secondIndexed.segment.translate
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation secondShift))) :
    Cell.sub firstShift secondShift ∈
      PeriodicGridDrawing.doubleNeighborTranslations := by
  exact
    PeriodicGridDrawing.relativeTranslate_isDoubleNeighbor_of_interiorsMeet
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_segmentEndpointsInExpandedSquare
        formula wellFormed degree isLocal clausesNonempty)
      firstMember secondMember meet

/-- A hypothetical contact involving at least one final noncarrier segment
has a neighboring relative lattice translation. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_relativeTranslate_mem_neighbor_of_interiorsMeet_of_not_carrier
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {firstIndexed secondIndexed : IndexedGridSegment}
    (firstMember :
      firstIndexed ∈
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).indexedSegments)
    (secondMember :
      secondIndexed ∈
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).indexedSegments)
    {firstShift secondShift : Cell}
    (firstWitness :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (secondWitness :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (notCarrier :
      (¬∃ link,
        firstWitness.routeWitness.metadata.source.component =
          DrawingPlanarSATComponent.carrier link) ∨
      ¬∃ link,
        secondWitness.routeWitness.metadata.source.component =
          DrawingPlanarSATComponent.carrier link)
    (meet :
      GridSegment.InteriorsMeet
        (firstIndexed.segment.translate
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation firstShift))
        (secondIndexed.segment.translate
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation secondShift))) :
    Cell.sub firstShift secondShift ∈
      neighborTranslations := by
  let drawing :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
      formula
  have expanded :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_segmentEndpointsInExpandedSquare
      formula wellFormed degree isLocal clausesNonempty
  rcases notCarrier with firstNotCarrier | secondNotCarrier
  · exact
      PeriodicGridDrawing.relativeTranslate_isNeighbor_of_interiorsMeet_of_firstHalfOpen
        (firstWitness.endpointsInHalfOpenFundamentalSquare_of_not_carrier
          formula wellFormed degree isLocal clausesNonempty
          firstNotCarrier)
        (expanded secondIndexed secondMember)
        meet
  · exact
      PeriodicGridDrawing.relativeTranslate_isNeighbor_of_interiorsMeet_of_secondHalfOpen
        (expanded firstIndexed firstMember)
        (secondWitness.endpointsInHalfOpenFundamentalSquare_of_not_carrier
          formula wellFormed degree isLocal clausesNonempty
          secondNotCarrier)
        meet

end PeriodicOrthocrossing
end LeanTrominoes
