import LeanTrominoes.RetainedFinalRouteCommonFrameSelections
import LeanTrominoes.RetainedFinalFlatNormalizedRouteSelections

/-!
# Route selections for arbitrary common component frames

The generic common-frame calculation remembers membership in the translated
source's local clause family.  Carrier-boundary bounds instead consume a
genuine route of a concrete finite incidence drawing.  This file supplies
that last bridge.

For a noncarrier, a retained source presentation with the same translated
component may differ only in enumeration bookkeeping.  For a carrier, raw
retained-link membership identifies the translated equality-lens formula
directly.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- A retained finite source presentation of a macrocell route in an
arbitrary common frame. -/
structure FinalGaugedCommonFrameMacrocellSource
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {clauseIndex literalIndex : Nat}
    {shift : Cell}
    (macrocell :
      FinalGaugedRouteMacrocellOccurrenceWitness
        formula clauseIndex literalIndex shift)
    (reindexShift : Cell) where
  source : DrawingPlanarSATClauseSource Variable
  sourceMember : source.RetainedComponentMember formula
  componentEq :
    source.component =
      (macrocell.commonFrameSource reindexShift).component
  localClauseIndexEq :
    source.localClauseIndex =
      (macrocell.commonFrameSource reindexShift).localClauseIndex

/-- A retained presentation of a translated noncarrier source selects the
exact common-frame final route. -/
theorem FinalGaugedCommonFrameMacrocellSource.exists_routeSelection
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {clauseIndex literalIndex : Nat}
    {shift reindexShift : Cell}
    {macrocell :
      FinalGaugedRouteMacrocellOccurrenceWitness
        formula clauseIndex literalIndex shift}
    (presentation :
      FinalGaugedCommonFrameMacrocellSource
        formula macrocell reindexShift) :
    Nonempty
      (FinalGaugedFlatNormalizedRouteSelection
        formula
        (macrocell.commonFrameRoute reindexShift, clauseIndex)
        presentation.source) := by
  rcases
      macrocell.exists_commonFrameClauseLiteral reindexShift with
    ⟨selection⟩
  have targetFormulaEq :
      presentation.source.clauseFormula formula =
        (macrocell.commonFrameSource reindexShift
          |>.clauseFormula formula) :=
    presentation.source.clauseFormula_eq_of_component_eq
      formula (macrocell.commonFrameSource reindexShift)
      presentation.componentEq
  have targetClauseMember :
      (selection.clause, presentation.source.localClauseIndex) ∈
        (presentation.source.clauseFormula formula).zipIdx := by
    rw [targetFormulaEq, presentation.localClauseIndexEq]
    exact selection.clauseMember
  let targetMetadata :
      DrawingPlanarSATClauseMetadata Variable :=
    ⟨selection.clause, presentation.source⟩
  have targetValid : targetMetadata.RetainedValid formula := by
    apply
      (targetMetadata
        |>.retainedValid_iff_sourceMember_and_localClauseMember
          formula).mpr
    exact ⟨presentation.sourceMember, targetClauseMember⟩
  have targetDrawingClauseMember :
      (selection.clause, presentation.source.localClauseIndex) ∈
        (presentation.source.incidenceDrawing formula).formula.zipIdx := by
    simpa only [targetMetadata] using
      targetMetadata.retainedLocalClauseMember
        wellFormed degree isLocal targetValid
  have drawingEq :
      presentation.source.incidenceDrawing formula =
        (macrocell.commonFrameSource reindexShift
          |>.incidenceDrawing formula) :=
    presentation.source.incidenceDrawing_eq_of_component_eq
      formula (macrocell.commonFrameSource reindexShift)
      presentation.componentEq
  exact ⟨{
    clause := selection.clause
    literal := selection.literal
    literalIndex := literalIndex
    clauseMember := targetDrawingClauseMember
    literalMember := selection.literalMember
    routeEq := by
      have routeEq := selection.routeEq
      rw [← drawingEq,
        ← presentation.localClauseIndexEq] at routeEq
      simpa only using routeEq
  }⟩

/-- A raw retained translate of an arbitrary selected carrier link selects
the exact common-frame final carrier route. -/
theorem FinalGaugedCarrierRouteOccurrenceWitness.exists_commonFrameRouteSelection
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {clauseIndex literalIndex : Nat}
    {shift : Cell}
    (carrier :
      FinalGaugedCarrierRouteOccurrenceWitness
        formula clauseIndex literalIndex shift)
    (reindexShift : Cell)
    (rawMember :
      carrierLinkPeriodTranslate formula.incidenceGraph
          carrier.link reindexShift ∈
        retainedDrawingCompleteCarrierLinksRaw formula.incidenceGraph) :
    ∃ localClauseIndex,
      Nonempty
        (FinalGaugedFlatNormalizedRouteSelection
          formula
          (carrier.commonFrameRoute reindexShift, clauseIndex)
          (.carrier
            (carrierLinkPeriodTranslate formula.incidenceGraph
              carrier.link reindexShift)
            localClauseIndex)) := by
  rcases
      carrier.metadata.source.exists_eq_carrier_of_component_eq
        carrier.link carrier.componentEq with
    ⟨localClauseIndex, sourceEq⟩
  rcases
      carrier.exists_commonFrameClauseLiteral reindexShift with
    ⟨selection⟩
  have sourceEq' :
      carrier.commonFrameSource reindexShift =
        .carrier
          (carrierLinkPeriodTranslate formula.incidenceGraph
            carrier.link reindexShift)
          localClauseIndex := by
    simp [FinalGaugedRouteOccurrenceWitness.commonFrameSource,
      sourceEq, DrawingPlanarSATClauseSource.periodTranslate]
  have carrierFormulaClauseMember :
      (selection.clause, localClauseIndex) ∈
        (drawingPlanarSATCarrierFormulaAt
          (Variable := Variable)
          (carrierLinkPeriodTranslate formula.incidenceGraph
            carrier.link reindexShift)).zipIdx := by
    simpa [sourceEq',
      DrawingPlanarSATClauseSource.clauseFormula,
      DrawingPlanarSATClauseSource.localClauseIndex] using
        selection.clauseMember
  have drawingClauseMember :
      (selection.clause, localClauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula
          (carrierLinkPeriodTranslate formula.incidenceGraph
            carrier.link reindexShift)).formula.zipIdx := by
    rw [
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_formula_of_raw
        wellFormed degree isLocal rawMember]
    exact carrierFormulaClauseMember
  refine ⟨localClauseIndex, ⟨{
    clause := selection.clause
    literal := selection.literal
    literalIndex := literalIndex
    clauseMember := ?_
    literalMember := selection.literalMember
    routeEq := ?_
  }⟩⟩
  · simpa [DrawingPlanarSATClauseSource.incidenceDrawing,
      DrawingPlanarSATClauseSource.localClauseIndex] using
      drawingClauseMember
  · have routeEq := selection.routeEq
    rw [sourceEq'] at routeEq
    simpa only [DrawingPlanarSATClauseSource.incidenceDrawing,
      DrawingPlanarSATClauseSource.localClauseIndex] using routeEq

end PeriodicOrthocrossing
end LeanTrominoes
