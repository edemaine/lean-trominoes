import LeanTrominoes.RetainedFinalFlatRouteMacrocellBounds
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierBoundingBox

/-!
# Bounding boxes for flat final carrier routes

Carrier lenses do not belong to a single planar-SAT macrocell, but every
selected retained lens lies in an explicit narrow rectangle along its source
corridor.  This file transfers that rectangle through clause-anchor
normalization to a flat route of the final periodic quotient.

Combining a carrier package with the existing noncarrier macrocell package
closes the directed source-prefix/fan case whenever their translated
rectangles are separated.  A failure of this test is therefore the precise
carrier--macrocell interface residue.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- Translating a point and both corners by the same offset preserves
membership in a closed grid rectangle. -/
theorem InClosedGridRectangle.add
    {lower upper point : Cell}
    (bounded : InClosedGridRectangle lower upper point)
    (offset : Cell) :
    InClosedGridRectangle
      (Cell.add offset lower)
      (Cell.add offset upper)
      (Cell.add offset point) := by
  rcases lower with ⟨lowerX, lowerY⟩
  rcases upper with ⟨upperX, upperY⟩
  rcases point with ⟨pointX, pointY⟩
  rcases offset with ⟨offsetX, offsetY⟩
  simp only [InClosedGridRectangle, Cell.add] at bounded ⊢
  omega

/-- A metadata-selected carrier route lies in the explicit rectangle of its
retained equality lens. -/
theorem DrawingPlanarSATClauseMetadata.localRoutePoint_in_carrierRectangle
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula)
    (link : EqualityLink CarrierNode)
    (componentEq :
      metadata.source.component = .carrier link)
    {literal : PlanarSATVariable Variable × Bool}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ metadata.clause.literals.zipIdx)
    {point : Cell}
    (pointMember :
      point ∈
        (metadata.source.incidenceDrawing formula).routes
          metadata.source.localClauseIndex literalIndex) :
    InClosedGridRectangle
      (drawingCompleteCarrierLinkRectangleLower
        formula.incidenceGraph link)
      (drawingCompleteCarrierLinkRectangleUpper
        formula.incidenceGraph link)
      point := by
  rcases metadata with ⟨clause, source⟩
  rcases source.exists_eq_carrier_of_component_eq
      link componentEq with
    ⟨localClauseIndex, sourceEq⟩
  subst source
  change
    link ∈ retainedDrawingCompleteCarrierLinks formula.incidenceGraph ∧
      (clause, localClauseIndex) ∈
        (drawingPlanarSATCarrierFormulaAt
          (Variable := Variable) link).zipIdx at valid
  have clauseMember :
      (clause, localClauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula link).formula.zipIdx := by
    rw [
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_formula
        wellFormed degree isLocal valid.1]
    exact valid.2
  exact
    (retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_bounded
      wellFormed degree isLocal valid.1).of_members
        clauseMember literalMember
        (by
          simpa [DrawingPlanarSATClauseSource.incidenceDrawing,
            DrawingPlanarSATClauseSource.localClauseIndex] using
              pointMember)

/-- A final route occurrence selected from a carrier component. -/
structure FinalGaugedFlatCarrierRouteWitness
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (taggedRoute : List Cell × Nat)
    extends FinalGaugedFlatRouteOccurrenceWitness formula taggedRoute where
  link : EqualityLink CarrierNode
  componentEq :
    toFinalGaugedFlatRouteOccurrenceWitness.routeWitness.metadata.source.component =
      .carrier link

/-- A recovered flat route occurrence has a carrier package whenever its
physical component is a carrier lens. -/
theorem
    FinalGaugedFlatRouteOccurrenceWitness.exists_carrierWitness_of_component_eq
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {taggedRoute : List Cell × Nat}
    (witness :
      FinalGaugedFlatRouteOccurrenceWitness
        formula taggedRoute)
    (link : EqualityLink CarrierNode)
    (componentEq :
      witness.routeWitness.metadata.source.component =
        .carrier link) :
    Nonempty
      (FinalGaugedFlatCarrierRouteWitness
        formula taggedRoute) :=
  ⟨{
    toFinalGaugedFlatRouteOccurrenceWitness := witness
    link := link
    componentEq := componentEq
  }⟩

/-- Physical translation applied to the carrier rectangle of a flat final
route occurrence. -/
def FinalGaugedFlatCarrierRouteWitness.physicalOffset
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {taggedRoute : List Cell × Nat}
    (witness :
      FinalGaugedFlatCarrierRouteWitness
        formula taggedRoute) :
    Cell :=
  (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
    formula).translation witness.routeWitness.physicalShift

/-- Lower corner of a flat carrier occurrence's translated lens rectangle. -/
def FinalGaugedFlatCarrierRouteWitness.rectangleLower
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {taggedRoute : List Cell × Nat}
    (witness :
      FinalGaugedFlatCarrierRouteWitness
        formula taggedRoute) :
    Cell :=
  Cell.add witness.physicalOffset
    (drawingCompleteCarrierLinkRectangleLower
      formula.incidenceGraph witness.link)

/-- Upper corner of a flat carrier occurrence's translated lens rectangle. -/
def FinalGaugedFlatCarrierRouteWitness.rectangleUpper
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {taggedRoute : List Cell × Nat}
    (witness :
      FinalGaugedFlatCarrierRouteWitness
        formula taggedRoute) :
    Cell :=
  Cell.add witness.physicalOffset
    (drawingCompleteCarrierLinkRectangleUpper
      formula.incidenceGraph witness.link)

/-- Every point of a flat final carrier route lies in its translated narrow
lens rectangle. -/
theorem
    FinalGaugedFlatCarrierRouteWitness.routePoints_in_rectangle
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {taggedRoute : List Cell × Nat}
    (witness :
      FinalGaugedFlatCarrierRouteWitness
        formula taggedRoute)
    {point : Cell}
    (pointMember : point ∈ taggedRoute.1) :
    InClosedGridRectangle
      witness.rectangleLower witness.rectangleUpper point := by
  rw [witness.finalRoute_eq_occurrence] at pointMember
  rw [witness.routeWitness.routeEq] at pointMember
  unfold metadataPhysicalRouteOccurrence at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨physicalPoint, physicalPointMember, pointEq⟩
  have physicalPointSourceMember :
      physicalPoint ∈
        (witness.routeWitness.metadata.source.incidenceDrawing
          formula).routes
          witness.routeWitness.metadata.source.localClauseIndex
          witness.coordinates.taggedLiteral.2 := by
    simpa [retainedDrawingPlanarSATLocalIncidenceDrawing_routes,
      retainedDrawingPlanarSATLocalIncidenceRoutes,
      metadataPhysicalIncidence,
      EmbeddedCNFIncidenceDrawing.routeAt,
      witness.routeWitness.metadataLookup] using physicalPointMember
  have physicalPointBounded :=
    witness.routeWitness.metadata.localRoutePoint_in_carrierRectangle
      wellFormed degree isLocal
      witness.routeWitness.metadata_retainedValid
      witness.link witness.componentEq
      witness.routeWitness.literalMember physicalPointSourceMember
  have translatedBounded :=
    InClosedGridRectangle.add
      physicalPointBounded witness.physicalOffset
  subst point
  simpa [FinalGaugedFlatCarrierRouteWitness.rectangleLower,
    FinalGaugedFlatCarrierRouteWitness.rectangleUpper,
    FinalGaugedFlatCarrierRouteWitness.physicalOffset,
    FinalGaugedRouteOccurrenceWitness.physicalShift] using
      translatedBounded

/-- A flat carrier source prefix and a flat noncarrier complete route have
the rasterization rectangle certificate whenever their translated
enclosing rectangles are separated. -/
theorem
    sourcePrefixPolylineRectanglesSeparated_of_flatCarrierMacrocell_rectanglesSeparated
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {sourceTaggedRoute referenceTaggedRoute : List Cell × Nat}
    (source :
      FinalGaugedFlatCarrierRouteWitness
        formula sourceTaggedRoute)
    (reference :
      FinalGaugedFlatRouteMacrocellWitness
        formula referenceTaggedRoute)
    (rectanglesSeparated :
      ClosedGridRectanglesSeparated
        source.rectangleLower source.rectangleUpper
        (planarSATMacrocellRouteLower reference.translatedCenter)
        (planarSATMacrocellRouteUpper reference.translatedCenter)) :
    PeriodicEightOccurrenceSplit.SourcePolylineRectanglesSeparated
      sourceTaggedRoute.1.dropLast referenceTaggedRoute.1 := by
  apply
    PeriodicEightOccurrenceSplit.SourcePolylineRectanglesSeparated.of_inSeparatedClosedGridRectangles
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
      formula wellFormed degree isLocal pointMember
  · exact rectanglesSeparated

end PeriodicOrthocrossing

namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- The separated carrier--macrocell branch of directed retained
source-prefix/fan separation, stated directly for flat final routes. -/
theorem
    retainedFinalSourceScaledPrefix_strictlyAvoids_otherOuterCompleteRoute_of_flatCarrierMacrocell_rectanglesSeparated
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
    {sourceRoute referenceRoute : List Cell}
    {sourceIndex referenceIndex : Nat}
    {sourcePoint referenceCenter : Cell}
    (sourceMember :
      (sourceRoute, sourceIndex) ∈
        (PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).edgeRoutes.zipIdx)
    (referenceMember :
      (referenceRoute, referenceIndex) ∈
        (PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).edgeRoutes.zipIdx)
    (sourceLength : 2 ≤ sourceRoute.length)
    (referenceLength : 2 ≤ referenceRoute.length)
    (indicesDifferent : sourceIndex ≠ referenceIndex)
    (sourceHead : sourceRoute.head? = some sourcePoint)
    (referenceLast :
      referenceRoute.getLast? = some referenceCenter)
    (sourceNeCenter : sourcePoint ≠ referenceCenter)
    (referenceTerminal : RetainedTerminalData)
    (referenceSlot : RetainedTerminalSlot)
    (referenceClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector referenceRoute) =
        some referenceTerminal)
    (sourceCarrier :
      PeriodicOrthocrossing.FinalGaugedFlatCarrierRouteWitness
        formula (sourceRoute, sourceIndex))
    (referenceMacrocell :
      PeriodicOrthocrossing.FinalGaugedFlatRouteMacrocellWitness
        formula (referenceRoute, referenceIndex))
    (rectanglesSeparated :
      ClosedGridRectanglesSeparated
        sourceCarrier.rectangleLower sourceCarrier.rectangleUpper
        (PeriodicOrthocrossing.planarSATMacrocellRouteLower
          referenceMacrocell.translatedCenter)
        (PeriodicOrthocrossing.planarSATMacrocellRouteUpper
          referenceMacrocell.translatedCenter)) :
    RoutesStrictlyAvoidEachOther
      (scalePolyline retainedTerminalFanTotalRefinement
        (scalePolyline factor sourceRoute)).dropLast
      (retainedTerminalFanOuterCompleteRoute
        (Cell.scale retainedTerminalFanTotalRefinement
          (Cell.scale factor referenceCenter))
        (scaleRetainedTerminalData factor referenceTerminal)
        referenceSlot) := by
  apply
    retainedFinalSourceScaledPrefix_strictlyAvoids_otherOuterCompleteRoute_of_sourcePolylineRectanglesSeparated
      formula wellFormed degree isLocal clausesNonempty
      factorGreaterThanOne clearance
      sourceMember referenceMember sourceLength referenceLength
      indicesDifferent sourceHead referenceLast sourceNeCenter
      referenceTerminal referenceSlot referenceClassified
  exact
    PeriodicOrthocrossing.sourcePrefixPolylineRectanglesSeparated_of_flatCarrierMacrocell_rectanglesSeparated
      formula wellFormed degree isLocal
      sourceCarrier referenceMacrocell rectanglesSeparated

end PeriodicEightOccurrenceSplit
end LeanTrominoes
