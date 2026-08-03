import LeanTrominoes.RetainedFinalRouteCarrierCrossoverNormalizedContact
import LeanTrominoes.PeriodicOrthocrossingPlanarSATSourceClauseTranslation

/-!
# Common-frame presentations of arbitrary final routes

The local carrier-boundary geometry is stated in a finite component frame,
whereas copied-source separation compares final route occurrences at
arbitrary period shifts.  A physical source translation by `reindexShift`
and a compensating translation of the final route put the same route in the
chosen finite frame.

This file packages that uniform calculation.  It also transports the
selected local clause and literal indices through source translation.  The
remaining component-specific work is only to identify the translated local
formula with the formula of the contact drawing.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- Physical offset which moves a final route occurrence into the finite
frame obtained by translating its local source by `reindexShift`. -/
def FinalGaugedRouteOccurrenceWitness.commonFrameOffset
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {clauseIndex literalIndex : Nat}
    {shift : Cell}
    (witness :
      FinalGaugedRouteOccurrenceWitness
        formula clauseIndex literalIndex shift)
    (reindexShift : Cell) : Cell :=
  carrierMacroPeriodTranslation formula.incidenceGraph
    (Cell.sub reindexShift witness.physicalShift)

/-- The final route occurrence expressed in the finite frame selected by
`reindexShift`. -/
def FinalGaugedRouteOccurrenceWitness.commonFrameRoute
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {clauseIndex literalIndex : Nat}
    {shift : Cell}
    (witness :
      FinalGaugedRouteOccurrenceWitness
        formula clauseIndex literalIndex shift)
    (reindexShift : Cell) : List Cell :=
  translatePolyline (witness.commonFrameOffset reindexShift)
    (finalGaugedRouteOccurrence
      formula clauseIndex literalIndex shift)

/-- Source selected by the same finite-frame reindexing. -/
def FinalGaugedRouteOccurrenceWitness.commonFrameSource
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {clauseIndex literalIndex : Nat}
    {shift : Cell}
    (witness :
      FinalGaugedRouteOccurrenceWitness
        formula clauseIndex literalIndex shift)
    (reindexShift : Cell) :
    DrawingPlanarSATClauseSource Variable :=
  witness.metadata.source.periodTranslate formula reindexShift

/-- Reindexing the source and compensating the final physical occurrence
produce literally the same selected route. -/
theorem FinalGaugedRouteOccurrenceWitness.commonFrameRoute_eq_sourceRoute
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {clauseIndex literalIndex : Nat}
    {shift : Cell}
    (witness :
      FinalGaugedRouteOccurrenceWitness
        formula clauseIndex literalIndex shift)
    (reindexShift : Cell) :
    witness.commonFrameRoute reindexShift =
      (witness.commonFrameSource reindexShift
        |>.incidenceDrawing formula).routes
          witness.metadata.source.localClauseIndex literalIndex := by
  have localRouteEq :
      (retainedDrawingPlanarSATLocalIncidenceDrawing formula).routeAt
          (metadataPhysicalIncidence
            witness.metadata witness.metadataIndex
            witness.literal literalIndex) =
        (witness.metadata.source.incidenceDrawing formula).routes
          witness.metadata.source.localClauseIndex literalIndex := by
    simp [retainedDrawingPlanarSATLocalIncidenceDrawing_routes,
      retainedDrawingPlanarSATLocalIncidenceRoutes,
      metadataPhysicalIncidence,
      EmbeddedCNFIncidenceDrawing.routeAt,
      witness.metadataLookup]
  change
    translatePolyline
        (carrierMacroPeriodTranslation formula.incidenceGraph
          (Cell.sub reindexShift witness.physicalShift))
        (finalGaugedRouteOccurrence
          formula clauseIndex literalIndex shift) = _
  rw [witness.routeEq]
  unfold metadataPhysicalRouteOccurrence
  rw [localRouteEq,
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_translation_eq_carrierMacro,
    translatePolyline_add]
  change
    translatePolyline
        (Cell.add
          (carrierMacroPeriodTranslation formula.incidenceGraph
            witness.physicalShift)
          (carrierMacroPeriodTranslation formula.incidenceGraph
            (Cell.sub reindexShift witness.physicalShift)))
        ((witness.metadata.source.incidenceDrawing formula).routes
          witness.metadata.source.localClauseIndex literalIndex) = _
  have offsetAdd :
      Cell.add
          (carrierMacroPeriodTranslation formula.incidenceGraph
            witness.physicalShift)
          (carrierMacroPeriodTranslation formula.incidenceGraph
            (Cell.sub reindexShift witness.physicalShift)) =
        carrierMacroPeriodTranslation formula.incidenceGraph
          reindexShift := by
    rcases witness.physicalShift with ⟨physicalX, physicalY⟩
    rcases reindexShift with ⟨reindexX, reindexY⟩
    apply Prod.ext <;>
      simp [carrierMacroPeriodTranslation,
        Cell.add, Cell.sub, Cell.scale] <;>
      ring
  rw [offsetAdd]
  unfold FinalGaugedRouteOccurrenceWitness.commonFrameSource
  exact
    (witness.metadata.source
      |>.incidenceDrawing_routes_periodTranslate
        formula reindexShift
        witness.metadata.source.localClauseIndex literalIndex).symm

/-- Clause and literal data for a final route after reindexing its local
source into an arbitrary finite frame.  Formula membership is deliberately
kept at the source-family level; each contact constructor later identifies
that formula with its concrete incidence drawing. -/
structure FinalGaugedCommonFrameClauseLiteral
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {clauseIndex literalIndex : Nat}
    {shift : Cell}
    (witness :
      FinalGaugedRouteOccurrenceWitness
        formula clauseIndex literalIndex shift)
    (reindexShift : Cell) where
  clause : EmbeddedClause (PlanarSATVariable Variable)
  literal : PlanarSATVariable Variable × Bool
  clauseMember :
    (clause,
        (witness.commonFrameSource reindexShift).localClauseIndex) ∈
      ((witness.commonFrameSource reindexShift).clauseFormula
        formula).zipIdx
  literalMember :
    (literal, literalIndex) ∈ clause.literals.zipIdx
  routeEq :
    witness.commonFrameRoute reindexShift =
      (witness.commonFrameSource reindexShift
        |>.incidenceDrawing formula).routes
          (witness.commonFrameSource reindexShift).localClauseIndex
          literalIndex

/-- Every recovered final route carries clause/literal selection data in
every common finite frame. -/
theorem FinalGaugedRouteOccurrenceWitness.exists_commonFrameClauseLiteral
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {clauseIndex literalIndex : Nat}
    {shift : Cell}
    (witness :
      FinalGaugedRouteOccurrenceWitness
        formula clauseIndex literalIndex shift)
    (reindexShift : Cell) :
    Nonempty
      (FinalGaugedCommonFrameClauseLiteral
        witness reindexShift) := by
  have sourceLocalClauseMember :
      (witness.metadata.clause,
          witness.metadata.source.localClauseIndex) ∈
        (witness.metadata.source.clauseFormula formula).zipIdx :=
    (witness.metadata
      |>.retainedValid_iff_sourceMember_and_localClauseMember
        formula).mp witness.metadata_retainedValid |>.2
  rcases
      witness.metadata.source.exists_periodTranslatedClauseLiteral
        formula reindexShift witness.metadata.clause
        sourceLocalClauseMember witness.literal literalIndex
        witness.literalMember with
    ⟨targetClause, targetLiteral,
      targetClauseMember, targetLiteralMember⟩
  refine ⟨{
    clause := targetClause
    literal := targetLiteral
    clauseMember := ?_
    literalMember := targetLiteralMember
    routeEq := ?_
  }⟩
  · simpa [FinalGaugedRouteOccurrenceWitness.commonFrameSource] using
      targetClauseMember
  · simpa [FinalGaugedRouteOccurrenceWitness.commonFrameSource,
      DrawingPlanarSATClauseSource.localClauseIndex_periodTranslate] using
      witness.commonFrameRoute_eq_sourceRoute reindexShift

end PeriodicOrthocrossing
end LeanTrominoes
