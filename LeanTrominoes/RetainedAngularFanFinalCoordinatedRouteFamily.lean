import LeanTrominoes.RetainedAngularFanFinalCoordinatedRouteValidity

/-!
# The final coordinated route family

This file lifts validity of one selected direct occurrence splice to the
entire final fixed-eight incidence family.  Copied source incidences use a
validated direct route when the selector succeeds and otherwise retain the
established source-scaled fan route.  Appended implication-cycle clauses
always take the latter fallback.

The resulting family has canonical endpoints and is pointwise orthogonal.
It is therefore ready for the separate global route-separation proof.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

set_option maxHeartbeats 2000000

private theorem coordinatedRoute_valid_of_choice_none
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
          formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (choiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex = none) :
    (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
      formula clauseIndex literalIndex).head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
              formula)
            clause) ∧
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula clauseIndex literalIndex).getLast? =
          some
            (PositionedPeriodicCNF.canonicalLiteralPosition
              (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
                formula)
              clause literal) ∧
      OrthogonalPolyline
        (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
          formula clauseIndex literalIndex) := by
  rw [
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_none
      formula clauseIndex literalIndex choiceNone]
  exact
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes_valid
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember

private theorem coordinatedRoute_valid_of_scaled_clause_none
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
          formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (scaledClauseNone :
      ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).scale retainedAngularFanSourceClearanceFactor).clauses[
          clauseIndex]? = none) :
    (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
      formula clauseIndex literalIndex).head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
              formula)
            clause) ∧
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula clauseIndex literalIndex).getLast? =
          some
            (PositionedPeriodicCNF.canonicalLiteralPosition
              (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
                formula)
              clause literal) ∧
      OrthogonalPolyline
        (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
          formula clauseIndex literalIndex) := by
  have routeEq :
      retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
          formula clauseIndex literalIndex =
        retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes
          formula clauseIndex literalIndex := by
    apply
      retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_clause_none
    exact scaledClauseNone
  rw [routeEq]
  exact
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes_valid
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember

/-- Every genuine incidence in the final coordinated family has its
canonical endpoints and is orthogonal. -/
theorem
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_valid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
          formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
      formula clauseIndex literalIndex).head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
              formula)
            clause) ∧
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula clauseIndex literalIndex).getLast? =
          some
            (PositionedPeriodicCNF.canonicalLiteralPosition
              (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
                formula)
              clause literal) ∧
      OrthogonalPolyline
        (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
          formula clauseIndex literalIndex) := by
  rw [retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula,
    retainedAngularFanSourceScaledRefinedFormula,
    retainedAngularFanRefinedFormula,
    PositionedPeriodicCNF.scale_clauses,
    List.zipIdx_map] at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨taggedClause, taggedClauseMember, taggedClauseEqual⟩
  rcases taggedClause with ⟨baseClause, baseIndex⟩
  have clauseIndexEqual :
      baseIndex = clauseIndex :=
    congrArg Prod.snd taggedClauseEqual
  have scaledClauseEqual :
      baseClause.scale retainedTerminalFanRoutingRefinement =
        clause :=
    congrArg Prod.fst taggedClauseEqual
  subst clauseIndex
  subst clause
  have baseLiteralMember :
      (literal, literalIndex) ∈ baseClause.literals.zipIdx := by
    simpa using literalMember
  let source :=
    (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula).scale retainedAngularFanSourceClearanceFactor
  let placement :=
    (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
      formula).scale retainedAngularFanSourceClearanceFactor
  let routes :=
    PositionedPeriodicCNF.scaleIncidenceRoutes
      retainedAngularFanSourceClearanceFactor
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        formula)
  let order :=
    angularOccurrenceOrder source.erase routes
  let occurrencePorts :=
    occurrencePortsOfAngularOrder source.erase order
  by_cases occurrenceIndex :
      baseIndex <
        (PeriodicEightOccurrenceSplitPositioned.occurrenceClauses
          source occurrencePorts).length
  · have copiedClauseMember :=
      occurrenceClauseMember_of_formula_member
        source placement order taggedClauseMember
        (by simpa [occurrencePorts] using occurrenceIndex)
    rcases occurrenceClauseMetadata_lookup
        source occurrencePorts copiedClauseMember with
      ⟨metadata, _metadataLookup, metadataClauseEqual,
        sourceClauseMember, metadataIndex,
        metadataClauseDefinition⟩
    have sourceClauseMemberAt :
        (metadata.sourceClause, baseIndex) ∈
          source.clauses.zipIdx := by
      simpa [metadataIndex] using sourceClauseMember
    have copiedClauseEqual :
        baseClause =
          occurrenceClause occurrencePorts baseIndex
            metadata.sourceClause := by
      calc
        baseClause = metadata.clause :=
          metadataClauseEqual.symm
        _ =
            occurrenceClause occurrencePorts
              metadata.clauseIndex metadata.sourceClause :=
          metadataClauseDefinition
        _ =
            occurrenceClause occurrencePorts
              baseIndex metadata.sourceClause := by
          rw [metadataIndex]
    rcases occurrenceLiteral_of_members
        occurrencePorts copiedClauseEqual baseLiteralMember with
      ⟨sourceLiteral, sourceLiteralMember,
        copiedLiteralEqual⟩
    dsimp only [source] at sourceClauseMemberAt
    rw [PositionedPeriodicCNF.scale_clauses,
      List.zipIdx_map] at sourceClauseMemberAt
    rcases List.mem_map.mp sourceClauseMemberAt with
      ⟨rawTaggedClause, rawTaggedClauseMember,
        rawTaggedClauseEqual⟩
    rcases rawTaggedClause with ⟨rawClause, rawIndex⟩
    have rawIndexEqual :
        rawIndex = baseIndex :=
      congrArg Prod.snd rawTaggedClauseEqual
    have rawScaledClauseEqual :
        rawClause.scale
            retainedAngularFanSourceClearanceFactor =
          metadata.sourceClause :=
      congrArg Prod.fst rawTaggedClauseEqual
    subst rawIndex
    have copiedClauseEqualRaw :
        baseClause =
          occurrenceClause occurrencePorts baseIndex
            (rawClause.scale
              retainedAngularFanSourceClearanceFactor) := by
      rw [copiedClauseEqual, rawScaledClauseEqual]
    have rawLiteralMember :
      (sourceLiteral, literalIndex) ∈
          rawClause.literals.zipIdx := by
      have scaledLiteralMember :
          (sourceLiteral, literalIndex) ∈
            (rawClause.scale
              retainedAngularFanSourceClearanceFactor).literals.zipIdx := by
        rw [rawScaledClauseEqual]
        exact sourceLiteralMember
      simpa using scaledLiteralMember
    cases choiceLookup :
        retainedFinalDirectSourceRouteChoice?
          formula baseIndex literalIndex with
    | none =>
        exact coordinatedRoute_valid_of_choice_none formula
          sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty
          (by
            rw [retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula,
              retainedAngularFanSourceScaledRefinedFormula,
              retainedAngularFanRefinedFormula,
              PositionedPeriodicCNF.scale_clauses,
              List.zipIdx_map]
            exact List.mem_map.mpr
              ⟨(baseClause, baseIndex),
                taggedClauseMember, rfl⟩)
          (by simpa using baseLiteralMember)
          choiceLookup
    | some choice =>
        have scaledClauseLookup :=
          (List.mem_zipIdx_iff_getElem?).mp
            (show
              (rawClause.scale
                  retainedAngularFanSourceClearanceFactor,
                baseIndex) ∈
                ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
                  formula).scale
                    retainedAngularFanSourceClearanceFactor).clauses.zipIdx
              by
                rw [PositionedPeriodicCNF.scale_clauses,
                  List.zipIdx_map]
                exact List.mem_map.mpr
                  ⟨(rawClause, baseIndex),
                    rawTaggedClauseMember, rfl⟩)
        have literalLookup :=
          (List.mem_zipIdx_iff_getElem?).mp rawLiteralMember
        rw [
          retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_some
            formula baseIndex literalIndex choice
            (rawClause.scale
              retainedAngularFanSourceClearanceFactor)
            sourceLiteral choiceLookup scaledClauseLookup literalLookup]
        have directValid :=
          retainedFinalCoordinatedDirectOccurrenceRoute_valid
            formula sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty choice
            rawTaggedClauseMember rawLiteralMember choiceLookup
        have copiedClausePosition :
            Cell.scale retainedTerminalFanTotalRefinement
                (PositionedPeriodicCNF.canonicalClausePosition
                  placement
                  (rawClause.scale
                    retainedAngularFanSourceClearanceFactor)) =
              Cell.scale retainedTerminalFanRoutingRefinement
                (PositionedPeriodicCNF.canonicalClausePosition
                  (PeriodicEightOccurrenceSplitPositioned.placement
                    placement)
                  (occurrenceClause occurrencePorts
                    baseIndex
                    (rawClause.scale
                      retainedAngularFanSourceClearanceFactor))) := by
          rw [canonicalClausePosition_occurrenceClause,
            Cell.scale_scale]
          simp [retainedTerminalFanTotalRefinement_eq,
            retainedTerminalFanRoutingRefinement,
            PeriodicEightOccurrenceSplitPositioned.refinementScale]
        constructor
        · rw [directValid.1, copiedClausePosition,
            copiedClauseEqualRaw]
          simp [retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement,
            retainedAngularFanSourceScaledRefinedPlacement,
            retainedAngularFanRefinedPlacement, placement]
        constructor
        · simpa [retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement,
            retainedAngularFanSourceScaledRefinedPlacement,
            retainedAngularFanRefinedPlacement,
            source, placement, routes, order, occurrencePorts,
            copiedClauseEqualRaw, copiedLiteralEqual] using
              directValid.2.1
        · exact directValid.2.2
  · have sourceIndexGe :
        source.clauses.length ≤ baseIndex := by
      simpa [PeriodicEightOccurrenceSplitPositioned.occurrenceClauses,
        source] using occurrenceIndex
    have scaledClauseLookup :
        source.clauses[baseIndex]? = none :=
      List.getElem?_eq_none_iff.mpr sourceIndexGe
    exact coordinatedRoute_valid_of_scaled_clause_none formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
      (by
        rw [retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula,
          retainedAngularFanSourceScaledRefinedFormula,
          retainedAngularFanRefinedFormula,
          PositionedPeriodicCNF.scale_clauses,
          List.zipIdx_map]
        exact List.mem_map.mpr
          ⟨(baseClause, baseIndex), taggedClauseMember, rfl⟩)
      (by simpa using baseLiteralMember)
      (by exact scaledClauseLookup)

/-- The final coordinated route family, packaged with canonical endpoints
and pointwise orthogonality. -/
def
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitCanonicalOrthogonalRoutes
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ []) :
    PositionedPeriodicCNF.CanonicalOrthogonalIncidenceRoutes
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        formula)
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
        formula) where
  routes :=
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
      formula
  endpoints := by
    intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    have valid :=
      retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_valid
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
    exact ⟨valid.1, valid.2.1⟩
  orthogonal := by
    intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    exact
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_valid
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember).2.2

end PeriodicOrthocrossing
end LeanTrominoes
