/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PolylineBoundingBoxRasterSeparation
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedNoncarrierPeriodicSeparation

/-!
# Macrocell bounds for final retained route occurrences

A route of the final periodic quotient remembers a physical route in the
finite retained planar-SAT drawing, together with the clause-anchor-adjusted
period shift that places it.  For a noncarrier component, the physical route
lies in one planar-SAT macrocell.  This file transfers that whole-route bound
through quotient normalization and periodic translation.

The resulting enclosing rectangles feed directly into the generic
source-prefix/fan raster-separation adapter.  Thus two noncarrier route
occurrences whose translated component centers differ require no local
terminal geometry.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- The finite-drawing period shift represented by a final route occurrence
after undoing clause-anchor normalization. -/
def FinalGaugedRouteOccurrenceWitness.physicalShift
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {clauseIndex literalIndex : Nat}
    {shift : Cell}
    (witness :
      FinalGaugedRouteOccurrenceWitness
        formula clauseIndex literalIndex shift) :
    Cell :=
  Cell.sub shift
    (PeriodicCNF.clauseAnchor
      (metadataGaugedPositionedClause
        formula witness.metadata).literals)

/-- The retained metadata lookup stored by a final route witness supplies
the validity certificate needed by its local component geometry. -/
theorem FinalGaugedRouteOccurrenceWitness.metadata_retainedValid
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {clauseIndex literalIndex : Nat}
    {shift : Cell}
    (witness :
      FinalGaugedRouteOccurrenceWitness
        formula clauseIndex literalIndex shift) :
    witness.metadata.RetainedValid formula := by
  have metadataMember :
      witness.metadata ∈
        retainedDrawingPlanarSATClauseMetadata formula :=
    List.mem_iff_getElem?.mpr
      ⟨witness.metadataIndex, witness.metadataLookup⟩
  exact retainedDrawingPlanarSATClauseMetadata_valid
    formula metadataMember

/-- The physical component center translated to the occurrence represented
by a final route witness. -/
def FinalGaugedRouteOccurrenceWitness.translatedMacrocellCenter
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {clauseIndex literalIndex : Nat}
    {shift : Cell}
    (witness :
      FinalGaugedRouteOccurrenceWitness
        formula clauseIndex literalIndex shift)
    (center : Cell) :
    Cell :=
  Cell.add center
    ((drawing formula.incidenceGraph).periodTranslation
      witness.physicalShift)

/-- Every point of a final noncarrier route occurrence lies in the
translated macrocell of its physical component. -/
theorem
    FinalGaugedRouteOccurrenceWitness.routePoints_in_translatedMacrocell
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {clauseIndex literalIndex : Nat}
    {shift : Cell}
    (witness :
      FinalGaugedRouteOccurrenceWitness
        formula clauseIndex literalIndex shift)
    (center : Cell)
    (centerEq :
      witness.metadata.source.component.macrocellCenter formula =
        some center)
    {point : Cell}
    (pointMember :
      point ∈
        finalGaugedRouteOccurrence
          formula clauseIndex literalIndex shift) :
    InPlanarSATMacrocell
      (witness.translatedMacrocellCenter center) point := by
  have notCarrier :
      ¬∃ link, witness.metadata.source.component = .carrier link := by
    rintro ⟨link, componentEq⟩
    rw [componentEq] at centerEq
    simp [DrawingPlanarSATComponent.macrocellCenter] at centerEq
  have valid :=
    witness.metadata.valid_of_retainedValid_of_not_carrier
      witness.metadata_retainedValid notCarrier
  rw [witness.routeEq] at pointMember
  unfold metadataPhysicalRouteOccurrence at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨physicalPoint, physicalPointMember, pointEq⟩
  have physicalPointSourceMember :
      physicalPoint ∈
        (witness.metadata.source.incidenceDrawing formula).routes
          witness.metadata.source.localClauseIndex literalIndex := by
    simpa [retainedDrawingPlanarSATLocalIncidenceDrawing_routes,
      retainedDrawingPlanarSATLocalIncidenceRoutes,
      metadataPhysicalIncidence,
      EmbeddedCNFIncidenceDrawing.routeAt,
      witness.metadataLookup] using physicalPointMember
  have physicalPointBounded :=
    witness.metadata.localRoutePoints_inPlanarSATMacrocell
      wellFormed degree isLocal valid center centerEq
      witness.literalMember physicalPointSourceMember
  have translatedBounded :=
    inPlanarSATMacrocell_translate
      (shift := witness.physicalShift)
      (drawingGridSize formula.incidenceGraph)
      physicalPointBounded
  subst point
  rw [
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_translation_eq_carrierMacro]
  simpa [FinalGaugedRouteOccurrenceWitness.translatedMacrocellCenter,
    FinalGaugedRouteOccurrenceWitness.physicalShift,
    carrierMacroPeriodTranslation,
    PeriodicGridDrawing.periodTranslation,
    Cell.add, Cell.scale, add_comm,
    mul_assoc, mul_comm, mul_left_comm] using
      translatedBounded

/-- Two final noncarrier route occurrences with distinct translated
component centers have the complete rectangle-separation certificate used
by retained-terminal rasterization. -/
theorem
    sourcePolylineRectanglesSeparated_of_finalRouteOccurrences_of_macrocellCenters_ne
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {firstClauseIndex firstLiteralIndex
      secondClauseIndex secondLiteralIndex : Nat}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedRouteOccurrenceWitness
        formula firstClauseIndex firstLiteralIndex firstShift)
    (second :
      FinalGaugedRouteOccurrenceWitness
        formula secondClauseIndex secondLiteralIndex secondShift)
    (firstCenter secondCenter : Cell)
    (firstCenterEq :
      first.metadata.source.component.macrocellCenter formula =
        some firstCenter)
    (secondCenterEq :
      second.metadata.source.component.macrocellCenter formula =
        some secondCenter)
    (centersDifferent :
      first.translatedMacrocellCenter firstCenter ≠
        second.translatedMacrocellCenter secondCenter) :
    PeriodicEightOccurrenceSplit.SourcePolylineRectanglesSeparated
      (finalGaugedRouteOccurrence
        formula firstClauseIndex firstLiteralIndex firstShift)
      (finalGaugedRouteOccurrence
        formula secondClauseIndex secondLiteralIndex secondShift) := by
  apply
    PeriodicEightOccurrenceSplit.SourcePolylineRectanglesSeparated.of_inSeparatedClosedGridRectangles
      (firstLower :=
        planarSATMacrocellRouteLower
          (first.translatedMacrocellCenter firstCenter))
      (firstUpper :=
        planarSATMacrocellRouteUpper
          (first.translatedMacrocellCenter firstCenter))
      (secondLower :=
        planarSATMacrocellRouteLower
          (second.translatedMacrocellCenter secondCenter))
      (secondUpper :=
        planarSATMacrocellRouteUpper
          (second.translatedMacrocellCenter secondCenter))
  · intro point pointMember
    exact first.routePoints_in_translatedMacrocell
      formula wellFormed degree isLocal firstCenter firstCenterEq
      pointMember
  · intro point pointMember
    exact second.routePoints_in_translatedMacrocell
      formula wellFormed degree isLocal secondCenter secondCenterEq
      pointMember
  · exact planarSATMacrocellRouteRectangles_separated centersDifferent

end PeriodicOrthocrossing
end LeanTrominoes
