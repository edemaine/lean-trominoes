import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATComponentSeparation
import LeanTrominoes.PeriodicOrthocrossingPlanarSATSourceClauseTranslation

/-!
# Separation after translating a retained carrier source

A selected carrier metadata entry can leave the selected representative
family after physical period translation while its link remains in the raw
retained window.  Clause and literal indices are nevertheless unchanged.
This file combines source-translation invariance with the raw carrier
component dispatcher.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- A period translate of a selected carrier metadata route avoids every
retained-valid noncarrier route whenever the translated link belongs to the
raw retained window and its first occurrence is neighboring. -/
theorem
    DrawingPlanarSATClauseMetadata.periodTranslate_localRoutes_avoidEachOther_of_raw_carrier
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (first second : DrawingPlanarSATClauseMetadata Variable)
    (firstValid : first.RetainedValid formula)
    (secondValid : second.RetainedValid formula)
    (shift : Cell)
    (link : EqualityLink CarrierNode)
    (localClauseIndex : Nat)
    (firstSourceEq :
      first.source = .carrier link localClauseIndex)
    (translatedLinkMember :
      carrierLinkPeriodTranslate formula.incidenceGraph link shift ∈
        retainedDrawingCompleteCarrierLinksRaw
          formula.incidenceGraph)
    (translatedFirstNeighbor :
      IsNeighborTranslation
        ((carrierLinkPeriodTranslate formula.incidenceGraph
          link shift).first.translate))
    {firstLiteral secondLiteral :
      PlanarSATVariable Variable × Bool}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        first.clause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        second.clause.literals.zipIdx)
    (secondNotCarrier :
      ¬∃ secondLink,
        second.source.component = .carrier secondLink) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      (((first.source.periodTranslate formula shift).incidenceDrawing
        formula).routes
          first.source.localClauseIndex firstLiteralIndex)
      ((second.source.incidenceDrawing formula).routes
        second.source.localClauseIndex secondLiteralIndex) := by
  have firstLocalClauseMember :
      (first.clause, first.source.localClauseIndex) ∈
        (first.source.clauseFormula formula).zipIdx :=
    (first.retainedValid_iff_sourceMember_and_localClauseMember
      formula).mp firstValid |>.2
  rcases
      first.source.exists_periodTranslatedClauseLiteral
        formula shift first.clause firstLocalClauseMember
        firstLiteral firstLiteralIndex firstLiteralMember with
    ⟨translatedClause, translatedLiteral,
      translatedClauseMember, translatedLiteralMember⟩
  have translatedSourceEq :
      first.source.periodTranslate formula shift =
        .carrier
          (carrierLinkPeriodTranslate
            formula.incidenceGraph link shift)
          localClauseIndex := by
    rw [firstSourceEq]
    rfl
  have firstLocalClauseIndexEq :
      first.source.localClauseIndex = localClauseIndex := by
    rw [firstSourceEq]
    rfl
  rw [translatedSourceEq] at translatedClauseMember
  have translatedFormulaClauseMember :
      (translatedClause, localClauseIndex) ∈
        (drawingPlanarSATCarrierFormulaAt
          (Variable := Variable)
          (carrierLinkPeriodTranslate
            formula.incidenceGraph link shift)).zipIdx := by
    simpa [DrawingPlanarSATClauseSource.localClauseIndex,
      DrawingPlanarSATClauseSource.clauseFormula] using
        translatedClauseMember
  have translatedClauseMember' :
      (translatedClause, localClauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula
          (carrierLinkPeriodTranslate
            formula.incidenceGraph link shift)).formula.zipIdx := by
    rw [
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_formula_of_raw
        wellFormed degree isLocal translatedLinkMember]
    exact translatedFormulaClauseMember
  rw [firstLocalClauseIndexEq, translatedSourceEq]
  exact
    retainedDrawingPlanarSATRawCarrier_routesAvoidEachOther_of_second_not_carrier
      formula wellFormed degree isLocal
      translatedLinkMember translatedFirstNeighbor
      translatedClauseMember' translatedLiteralMember
      second secondValid secondLiteralMember secondNotCarrier

/-- Two independently translated metadata routes avoid one another when the
first becomes a neighboring raw carrier and the second translated
noncarrier source remains in the retained component family. -/
theorem
    DrawingPlanarSATClauseMetadata.two_periodTranslate_localRoutes_avoidEachOther_of_raw_carrier
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (first second : DrawingPlanarSATClauseMetadata Variable)
    (firstValid : first.RetainedValid formula)
    (secondValid : second.RetainedValid formula)
    (firstShift secondShift : Cell)
    (link : EqualityLink CarrierNode)
    (localClauseIndex : Nat)
    (firstSourceEq :
      first.source = .carrier link localClauseIndex)
    (translatedLinkMember :
      carrierLinkPeriodTranslate formula.incidenceGraph link firstShift ∈
        retainedDrawingCompleteCarrierLinksRaw
          formula.incidenceGraph)
    (translatedFirstNeighbor :
      IsNeighborTranslation
        ((carrierLinkPeriodTranslate formula.incidenceGraph
          link firstShift).first.translate))
    (translatedSecondMember :
      (second.source.periodTranslate formula secondShift)
        |>.RetainedComponentMember formula)
    {firstLiteral secondLiteral :
      PlanarSATVariable Variable × Bool}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        first.clause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        second.clause.literals.zipIdx)
    (secondNotCarrier :
      ¬∃ secondLink,
        second.source.component = .carrier secondLink) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      (((first.source.periodTranslate formula firstShift).incidenceDrawing
        formula).routes
          first.source.localClauseIndex firstLiteralIndex)
      (((second.source.periodTranslate formula secondShift).incidenceDrawing
        formula).routes
          second.source.localClauseIndex secondLiteralIndex) := by
  have secondLocalClauseMember :
      (second.clause, second.source.localClauseIndex) ∈
        (second.source.clauseFormula formula).zipIdx :=
    (second.retainedValid_iff_sourceMember_and_localClauseMember
      formula).mp secondValid |>.2
  rcases
      second.source.exists_periodTranslatedClauseLiteral
        formula secondShift second.clause secondLocalClauseMember
        secondLiteral secondLiteralIndex secondLiteralMember with
    ⟨translatedSecondClause, translatedSecondLiteral,
      translatedSecondClauseMember,
      translatedSecondLiteralMember⟩
  let translatedSecond :
      DrawingPlanarSATClauseMetadata Variable :=
    ⟨translatedSecondClause,
      second.source.periodTranslate formula secondShift⟩
  have translatedSecondValid :
      translatedSecond.RetainedValid formula := by
    apply
      (translatedSecond
        |>.retainedValid_iff_sourceMember_and_localClauseMember
          formula).mpr
    exact ⟨translatedSecondMember,
      translatedSecondClauseMember⟩
  have translatedSecondNotCarrier :
      ¬∃ secondLink,
        translatedSecond.source.component = .carrier secondLink := by
    rintro ⟨secondLink, translatedCarrier⟩
    apply secondNotCarrier
    rcases second with ⟨secondClause, secondSource⟩
    cases secondSource <;>
      simp_all [translatedSecond,
        DrawingPlanarSATClauseSource.periodTranslate,
        DrawingPlanarSATClauseSource.component]
  have avoid :=
    first.periodTranslate_localRoutes_avoidEachOther_of_raw_carrier
      wellFormed degree isLocal translatedSecond
      firstValid translatedSecondValid firstShift
      link localClauseIndex firstSourceEq
      translatedLinkMember translatedFirstNeighbor
      firstLiteralMember translatedSecondLiteralMember
      translatedSecondNotCarrier
  simpa only [translatedSecond,
    DrawingPlanarSATClauseSource.localClauseIndex_periodTranslate] using
      avoid

end PeriodicOrthocrossing
end LeanTrominoes
