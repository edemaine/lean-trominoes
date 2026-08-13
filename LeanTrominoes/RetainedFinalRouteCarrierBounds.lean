/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedFinalFlatCarrierRouteBounds
import LeanTrominoes.RetainedFinalRouteMacrocellShapeClassification

/-!
# Carrier bounds for arbitrary final route occurrences

Carrier lenses do not fit in a planar-SAT macrocell.  Their local drawing is
nevertheless contained in an explicit narrow rectangle.  This file transports
that rectangle through the anchor-adjusted physical shift of an arbitrary
final quotient occurrence and pairs it with the shift-parametric macrocell
wrapper.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- An arbitrary final route occurrence selected from a carrier component. -/
structure FinalGaugedCarrierRouteOccurrenceWitness
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat)
    (shift : Cell)
    extends
      FinalGaugedRouteOccurrenceWitness
        formula clauseIndex literalIndex shift where
  link : EqualityLink CarrierNode
  componentEq :
    toFinalGaugedRouteOccurrenceWitness.metadata.source.component =
      .carrier link

/-- A route occurrence has a carrier package whenever its physical metadata
selects a retained equality lens. -/
theorem
    FinalGaugedRouteOccurrenceWitness.exists_carrierOccurrenceWitness_of_component_eq
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {clauseIndex literalIndex : Nat}
    {shift : Cell}
    (witness :
      FinalGaugedRouteOccurrenceWitness
        formula clauseIndex literalIndex shift)
    (link : EqualityLink CarrierNode)
    (componentEq :
      witness.metadata.source.component = .carrier link) :
    Nonempty
      (FinalGaugedCarrierRouteOccurrenceWitness
        formula clauseIndex literalIndex shift) :=
  ⟨{
    toFinalGaugedRouteOccurrenceWitness := witness
    link := link
    componentEq := componentEq
  }⟩

/-- Physical translation applied to the carrier lens rectangle. -/
def FinalGaugedCarrierRouteOccurrenceWitness.physicalOffset
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {clauseIndex literalIndex : Nat}
    {shift : Cell}
    (witness :
      FinalGaugedCarrierRouteOccurrenceWitness
        formula clauseIndex literalIndex shift) :
    Cell :=
  (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
    formula).translation witness.physicalShift

/-- Lower corner of the translated carrier lens rectangle. -/
def FinalGaugedCarrierRouteOccurrenceWitness.rectangleLower
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {clauseIndex literalIndex : Nat}
    {shift : Cell}
    (witness :
      FinalGaugedCarrierRouteOccurrenceWitness
        formula clauseIndex literalIndex shift) :
    Cell :=
  Cell.add witness.physicalOffset
    (drawingCompleteCarrierLinkRectangleLower
      formula.incidenceGraph witness.link)

/-- Upper corner of the translated carrier lens rectangle. -/
def FinalGaugedCarrierRouteOccurrenceWitness.rectangleUpper
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {clauseIndex literalIndex : Nat}
    {shift : Cell}
    (witness :
      FinalGaugedCarrierRouteOccurrenceWitness
        formula clauseIndex literalIndex shift) :
    Cell :=
  Cell.add witness.physicalOffset
    (drawingCompleteCarrierLinkRectangleUpper
      formula.incidenceGraph witness.link)

/-- Every point of an arbitrary final carrier occurrence lies in its
translated narrow lens rectangle. -/
theorem
    FinalGaugedCarrierRouteOccurrenceWitness.routePoints_in_rectangle
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {clauseIndex literalIndex : Nat}
    {shift : Cell}
    (witness :
      FinalGaugedCarrierRouteOccurrenceWitness
        formula clauseIndex literalIndex shift)
    {point : Cell}
    (pointMember :
      point ∈
        finalGaugedRouteOccurrence
          formula clauseIndex literalIndex shift) :
    InClosedGridRectangle
      witness.rectangleLower witness.rectangleUpper point := by
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
    witness.metadata.localRoutePoint_in_carrierRectangle
      wellFormed degree isLocal
      witness.metadata_retainedValid
      witness.link witness.componentEq
      witness.literalMember physicalPointSourceMember
  have translatedBounded :=
    InClosedGridRectangle.add
      physicalPointBounded witness.physicalOffset
  subst point
  simpa [FinalGaugedCarrierRouteOccurrenceWitness.rectangleLower,
    FinalGaugedCarrierRouteOccurrenceWitness.rectangleUpper,
    FinalGaugedCarrierRouteOccurrenceWitness.physicalOffset,
    FinalGaugedRouteOccurrenceWitness.physicalShift] using
      translatedBounded

/-- Every final route occurrence packages either as a carrier lens or as a
noncarrier macrocell. -/
theorem
    FinalGaugedRouteOccurrenceWitness.exists_carrier_or_macrocellOccurrenceWitness
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {clauseIndex literalIndex : Nat}
    {shift : Cell}
    (witness :
      FinalGaugedRouteOccurrenceWitness
        formula clauseIndex literalIndex shift) :
    Nonempty
        (FinalGaugedCarrierRouteOccurrenceWitness
          formula clauseIndex literalIndex shift) ∨
      Nonempty
        (FinalGaugedRouteMacrocellOccurrenceWitness
          formula clauseIndex literalIndex shift) := by
  by_cases carrier :
      ∃ link,
        witness.metadata.source.component = .carrier link
  · rcases carrier with ⟨link, componentEq⟩
    exact Or.inl
      (witness.exists_carrierOccurrenceWitness_of_component_eq
        link componentEq)
  · exact Or.inr
      (witness.exists_macrocellOccurrenceWitness_of_not_carrier
        carrier)

/-- A carrier source prefix and a noncarrier complete route have the
rasterization rectangle certificate whenever their occurrence rectangles
are separated. -/
theorem
    sourcePrefixPolylineRectanglesSeparated_of_carrierMacrocellOccurrences_of_rectanglesSeparated
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {sourceClauseIndex sourceLiteralIndex
      referenceClauseIndex referenceLiteralIndex : Nat}
    {sourceShift referenceShift : Cell}
    (source :
      FinalGaugedCarrierRouteOccurrenceWitness
        formula sourceClauseIndex sourceLiteralIndex sourceShift)
    (reference :
      FinalGaugedRouteMacrocellOccurrenceWitness
        formula referenceClauseIndex referenceLiteralIndex referenceShift)
    (rectanglesSeparated :
      ClosedGridRectanglesSeparated
        source.rectangleLower source.rectangleUpper
        (planarSATMacrocellRouteLower reference.translatedCenter)
        (planarSATMacrocellRouteUpper reference.translatedCenter)) :
    SourcePolylineRectanglesSeparated
      (finalGaugedRouteOccurrence
        formula sourceClauseIndex sourceLiteralIndex sourceShift).dropLast
      (finalGaugedRouteOccurrence
        formula referenceClauseIndex referenceLiteralIndex referenceShift) := by
  apply
    SourcePolylineRectanglesSeparated.of_inSeparatedClosedGridRectangles
      (firstLower := source.rectangleLower)
      (firstUpper := source.rectangleUpper)
      (secondLower :=
        planarSATMacrocellRouteLower reference.translatedCenter)
      (secondUpper :=
        planarSATMacrocellRouteUpper reference.translatedCenter)
  · intro point pointMember
    exact source.routePoints_in_rectangle
      formula wellFormed degree isLocal
      (List.mem_of_mem_dropLast pointMember)
  · intro point pointMember
    exact reference.routePoints_in_translatedMacrocell
      formula wellFormed degree isLocal
      reference.center reference.centerEq pointMember
  · exact rectanglesSeparated

end PeriodicOrthocrossing
end LeanTrominoes
