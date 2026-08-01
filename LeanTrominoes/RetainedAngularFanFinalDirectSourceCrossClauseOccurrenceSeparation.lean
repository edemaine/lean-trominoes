import LeanTrominoes.RetainedAngularFanFinalDirectSourceCrossClauseSeparation
import LeanTrominoes.RetainedAngularFanFinalDirectSourceOwnCycleSeparation

/-!
# Cross-clause separation for actual final direct occurrences

The choice-level cross-clause theorem is stated for complete Figure 7 atlas
routes.  Successful final choices identify those routes with both the
explicit coordinated occurrences and the public total route-family entries.
This file transports strict separation across those identifications.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Explicit coordinated direct occurrences from different copied source
clauses are strictly separated. -/
theorem
    retainedFinalCoordinatedDirectOccurrenceRoutes_crossClause_strictlyAvoid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (firstChoice secondChoice : RetainedDirectSourceRouteChoice)
    {firstClause secondClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx)
    (firstChoiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula firstClauseIndex firstLiteralIndex =
        some firstChoice)
    (secondChoiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula secondClauseIndex secondLiteralIndex =
        some secondChoice)
    (clauseIndicesDifferent :
      firstClauseIndex ≠ secondClauseIndex) :
    RoutesStrictlyAvoidEachOther
      (retainedFinalCoordinatedDirectOccurrenceRoute
        formula firstChoice
        (firstClause.scale retainedAngularFanSourceClearanceFactor)
        firstLiteral firstClauseIndex firstLiteralIndex)
      (retainedFinalCoordinatedDirectOccurrenceRoute
        formula secondChoice
        (secondClause.scale retainedAngularFanSourceClearanceFactor)
        secondLiteral secondClauseIndex secondLiteralIndex) := by
  rw [
    retainedFinalCoordinatedDirectOccurrenceRoute_eq_completeFigure7Route
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty firstChoice
      firstClauseMember firstLiteralMember firstChoiceLookup,
    retainedFinalCoordinatedDirectOccurrenceRoute_eq_completeFigure7Route
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty secondChoice
      secondClauseMember secondLiteralMember secondChoiceLookup]
  exact
    retainedFinalDirectSourceCrossClause_completeFigure7Routes_strictlyAvoid
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty firstChoice secondChoice
      firstClauseMember secondClauseMember
      firstLiteralMember secondLiteralMember
      firstChoiceLookup secondChoiceLookup clauseIndicesDifferent

/-- Public coordinated routes selected successfully from different copied
source clauses avoid each other. -/
theorem
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_crossClause_avoidEachOther_of_choices_some
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (firstChoice secondChoice : RetainedDirectSourceRouteChoice)
    {firstClause secondClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx)
    (firstChoiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula firstClauseIndex firstLiteralIndex =
        some firstChoice)
    (secondChoiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula secondClauseIndex secondLiteralIndex =
        some secondChoice)
    (clauseIndicesDifferent :
      firstClauseIndex ≠ secondClauseIndex) :
    RoutesAvoidEachOther
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula firstClauseIndex firstLiteralIndex)
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula secondClauseIndex secondLiteralIndex) := by
  have firstScaledClauseMember :
      (firstClause.scale retainedAngularFanSourceClearanceFactor,
          firstClauseIndex) ∈
        ((finalCoordinatedSource formula).scale
          retainedAngularFanSourceClearanceFactor).clauses.zipIdx := by
    rw [PositionedPeriodicCNF.scale_clauses, List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(firstClause, firstClauseIndex), firstClauseMember, rfl⟩
  have secondScaledClauseMember :
      (secondClause.scale retainedAngularFanSourceClearanceFactor,
          secondClauseIndex) ∈
        ((finalCoordinatedSource formula).scale
          retainedAngularFanSourceClearanceFactor).clauses.zipIdx := by
    rw [PositionedPeriodicCNF.scale_clauses, List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(secondClause, secondClauseIndex), secondClauseMember, rfl⟩
  have firstScaledClauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp firstScaledClauseMember
  have secondScaledClauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp secondScaledClauseMember
  have firstLiteralLookup :
      (firstClause.scale retainedAngularFanSourceClearanceFactor).literals[
          firstLiteralIndex]? =
        some firstLiteral := by
    simpa using
      (List.mem_zipIdx_iff_getElem?).mp firstLiteralMember
  have secondLiteralLookup :
      (secondClause.scale retainedAngularFanSourceClearanceFactor).literals[
          secondLiteralIndex]? =
        some secondLiteral := by
    simpa using
      (List.mem_zipIdx_iff_getElem?).mp secondLiteralMember
  rw [
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_some
      formula firstClauseIndex firstLiteralIndex firstChoice
      (firstClause.scale retainedAngularFanSourceClearanceFactor)
      firstLiteral firstChoiceLookup
      firstScaledClauseLookup firstLiteralLookup,
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_some
      formula secondClauseIndex secondLiteralIndex secondChoice
      (secondClause.scale retainedAngularFanSourceClearanceFactor)
      secondLiteral secondChoiceLookup
      secondScaledClauseLookup secondLiteralLookup]
  exact
    (retainedFinalCoordinatedDirectOccurrenceRoutes_crossClause_strictlyAvoid
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty firstChoice secondChoice
      firstClauseMember secondClauseMember
      firstLiteralMember secondLiteralMember
      firstChoiceLookup secondChoiceLookup
      clauseIndicesDifferent).toRoutesAvoidEachOther

end PeriodicOrthocrossing
end LeanTrominoes
