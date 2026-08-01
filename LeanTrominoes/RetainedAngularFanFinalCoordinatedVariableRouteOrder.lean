import LeanTrominoes.RetainedAngularFanSourceScaledVariableRouteOrder
import LeanTrominoes.RetainedAngularFanFinalCoordinatedRouteFamily
import LeanTrominoes.RetainedAngularFanFinalFallbackOccurrenceSeparation

/-!
# Variable route order for the final coordinated family

The coordinated family differs from the established source-scaled retained
family only on copied source incidences.  Successful direct choices and the
singleton-prefix delayed-lane fallback both retain the exact final Figure 7
spoke; every other copied route and every implication-cycle route is
unchanged.  Memberwise terminal-direction transport therefore gives the
same clockwise occurrence order.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

set_option maxHeartbeats 2000000

private theorem finalCoordinatedScaledClause?_eq_some_of_mem_for_route_order
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).clauses.zipIdx) :
    finalCoordinatedScaledClause? formula clauseIndex =
      some
        (clause.scale retainedAngularFanSourceClearanceFactor) := by
  have clauseLookup :
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).clauses[clauseIndex]? = some clause :=
    (List.mem_zipIdx_iff_getElem?
      (x := (clause, clauseIndex))
      (l :=
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).clauses)).mp clauseMember
  unfold finalCoordinatedScaledClause? finalCoordinatedSource
  rw [PositionedPeriodicCNF.scale_clauses, List.getElem?_map,
    clauseLookup]
  rfl

private theorem finalCoordinatedScaledClause?_eq_none_of_length_le_for_route_order
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex : Nat)
    (indexGe :
      ((finalCoordinatedSource formula).scale
        retainedAngularFanSourceClearanceFactor).clauses.length ≤
          clauseIndex) :
    finalCoordinatedScaledClause? formula clauseIndex = none := by
  exact List.getElem?_eq_none_iff.mpr indexGe

/-- Every genuine coordinated route has the same terminal direction as the
established source-scaled retained route at the same incidence index. -/
theorem
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_lastDirection_eq_fallback
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
    AxisDirection.polylineLastDirection
        (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
          formula clauseIndex literalIndex) =
      AxisDirection.polylineLastDirection
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes
          formula clauseIndex literalIndex) := by
  let sourceCertificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let retainedClausesNonempty :=
    retainedDrawingPlanarSATFormula_clausesNonempty_of_source
      formula sourceClausesNonempty
  let family :
      PositionedPeriodicCNF.CanonicalRetainedRayIncidenceRoutes
        (finalCoordinatedSource formula)
        (finalCoordinatedPlacement formula) :=
    { routes := finalCoordinatedSourceRoutes formula
      endpoints := by
        intro sourceClause sourceClauseIndex sourceClauseMember
          sourceLiteral sourceLiteralIndex sourceLiteralMember
        exact
          retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_endpoints
            formula
            sourceCertificate.graphWellFormed
            sourceCertificate.graphDegreeAtMostThree
            sourceCertificate.graphIsLocal
            sourceClauseMember sourceLiteralMember
      retained := by
        intro sourceClause sourceClauseIndex sourceClauseMember
          sourceLiteral sourceLiteralIndex sourceLiteralMember
        exact
          retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_retainedRay
            formula
            sourceCertificate.graphWellFormed
            sourceCertificate.graphDegreeAtMostThree
            sourceCertificate.graphIsLocal
            retainedClausesNonempty
            (sourceClause, sourceClauseIndex) sourceClauseMember
            (sourceLiteral, sourceLiteralIndex) sourceLiteralMember }
  have familyFits :
      FitsEightSlots
        (angularOccurrenceOrder
          (finalCoordinatedSource formula).erase
          family.routes) := by
    simpa [finalCoordinatedSource, finalCoordinatedSourceRoutes,
      retainedDrawingAngularOccurrenceOrder,
      retainedPlanarSATFormula, family] using
      retainedDrawingAngularOccurrenceOrder_fitsEightSlots
        sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
  have familyCertificate :
      RetainedOccurrenceTerminalCertificate
        (finalCoordinatedSource formula).erase
        family.routes := by
    simpa only [family, finalCoordinatedSource,
      finalCoordinatedSourceRoutes] using
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATOccurrence_terminalCertificate
        formula
        sourceCertificate.graphWellFormed
        sourceCertificate.graphDegreeAtMostThree
        sourceCertificate.graphIsLocal
        retainedClausesNonempty
  have familyLengths :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈
          (finalCoordinatedSource formula).clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
            sourceClause.literals.zipIdx →
          2 ≤
            (family.routes
              sourceClauseIndex sourceLiteralIndex).length := by
    intro sourceClause sourceClauseIndex sourceClauseMember
      sourceLiteral sourceLiteralIndex sourceLiteralMember
    simpa only [family, finalCoordinatedSourceRoutes] using
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_length_ge_two
        formula
        sourceCertificate.graphWellFormed
        sourceCertificate.graphDegreeAtMostThree
        sourceCertificate.graphIsLocal
        retainedClausesNonempty
        sourceClauseMember sourceLiteralMember
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
  let scaledSource :=
    (finalCoordinatedSource formula).scale
      retainedAngularFanSourceClearanceFactor
  let scaledPlacement :=
    (finalCoordinatedPlacement formula).scale
      retainedAngularFanSourceClearanceFactor
  let scaledRoutes :=
    PositionedPeriodicCNF.scaleIncidenceRoutes
      retainedAngularFanSourceClearanceFactor
      (finalCoordinatedSourceRoutes formula)
  let order :=
    angularOccurrenceOrder scaledSource.erase scaledRoutes
  let occurrencePorts :=
    occurrencePortsOfAngularOrder scaledSource.erase order
  by_cases occurrenceIndex :
      baseIndex <
        (PeriodicEightOccurrenceSplitPositioned.occurrenceClauses
          scaledSource occurrencePorts).length
  · have copiedClauseMember :=
      occurrenceClauseMember_of_formula_member
        scaledSource scaledPlacement order taggedClauseMember
        (by simpa [occurrencePorts] using occurrenceIndex)
    rcases
        occurrenceClauseMetadata_lookup
          scaledSource occurrencePorts copiedClauseMember with
      ⟨metadata, _metadataLookup, metadataClauseEqual,
        scaledSourceClauseMember, metadataIndex,
        metadataClauseDefinition⟩
    have scaledSourceClauseMemberAt :
        (metadata.sourceClause, baseIndex) ∈
          scaledSource.clauses.zipIdx := by
      simpa [metadataIndex] using scaledSourceClauseMember
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
    rcases
        occurrenceLiteral_of_members
          occurrencePorts copiedClauseEqual baseLiteralMember with
      ⟨sourceLiteral, sourceLiteralMember,
        _copiedLiteralEqual⟩
    dsimp only [scaledSource] at scaledSourceClauseMemberAt
    rw [PositionedPeriodicCNF.scale_clauses,
      List.zipIdx_map] at scaledSourceClauseMemberAt
    rcases List.mem_map.mp scaledSourceClauseMemberAt with
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
    have scaledClauseLookup :
        finalCoordinatedScaledClause?
            formula baseIndex =
          some
            (rawClause.scale
              retainedAngularFanSourceClearanceFactor) :=
      finalCoordinatedScaledClause?_eq_some_of_mem_for_route_order
        formula rawTaggedClauseMember
    have literalLookup :
        rawClause.literals[literalIndex]? =
          some sourceLiteral :=
      (List.mem_zipIdx_iff_getElem?).mp rawLiteralMember
    have fallbackOccurrence :
        retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes
            formula baseIndex literalIndex =
          retainedAngularFanSplicedOccurrenceRoute
            scaledSource scaledPlacement scaledRoutes
            (rawClause.scale
              retainedAngularFanSourceClearanceFactor)
            sourceLiteral baseIndex literalIndex := by
      simpa [scaledSource, scaledPlacement, scaledRoutes] using
        retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes_eq_splicedOccurrenceRoute
          formula rawTaggedClauseMember rawLiteralMember
    have fallbackDirection :
        AxisDirection.polylineLastDirection
            (retainedAngularFanSplicedOccurrenceRoute
              scaledSource scaledPlacement scaledRoutes
              (rawClause.scale
                retainedAngularFanSourceClearanceFactor)
              sourceLiteral baseIndex literalIndex) =
          AxisDirection.polylineLastDirection
            (angularOccurrenceSuffix
              scaledPlacement
              (angularOccurrenceOrder
                scaledSource.erase scaledRoutes)
              (rawClause.scale
                retainedAngularFanSourceClearanceFactor)
              sourceLiteral baseIndex literalIndex) := by
      simpa [scaledSource, scaledPlacement, scaledRoutes,
        family, finalCoordinatedSource,
        finalCoordinatedPlacement,
        finalCoordinatedSourceRoutes] using
        retainedAngularFanSourceScaledSplicedOccurrenceRoute_lastDirection
          retainedAngularFanSourceClearanceFactor_pos
          (finalCoordinatedSource formula)
          (finalCoordinatedPlacement formula)
          family familyFits familyCertificate familyLengths
          rawTaggedClauseMember rawLiteralMember
    cases choiceLookup :
        retainedFinalDirectSourceRouteChoice?
          formula baseIndex literalIndex with
    | none =>
        by_cases prefixLength :
            (finalCoordinatedSourceRoutes
              formula baseIndex literalIndex).dropLast.length = 1
        · rw [
            retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_none_of_prefix_length_one
              formula baseIndex literalIndex
              (rawClause.scale
                retainedAngularFanSourceClearanceFactor)
            sourceLiteral choiceLookup prefixLength
              scaledClauseLookup literalLookup,
            fallbackOccurrence]
          have escapedDirection :
              AxisDirection.polylineLastDirection
                  (retainedFinalEscapedFallbackOccurrenceRoute
                    formula
                    (rawClause.scale
                      retainedAngularFanSourceClearanceFactor)
                    sourceLiteral baseIndex literalIndex) =
                AxisDirection.polylineLastDirection
                  (angularOccurrenceSuffix
                    scaledPlacement
                    (angularOccurrenceOrder
                      scaledSource.erase scaledRoutes)
                    (rawClause.scale
                      retainedAngularFanSourceClearanceFactor)
                    sourceLiteral baseIndex literalIndex) := by
            simpa [scaledSource, scaledPlacement, scaledRoutes,
              finalCoordinatedSource,
              finalCoordinatedPlacement,
              finalCoordinatedSourceRoutes] using
              retainedFinalEscapedFallbackOccurrenceRoute_lastDirection
                formula sourceLocal sourceWidth sourceOccurrences
                sourceClausesNonempty
                rawTaggedClauseMember rawLiteralMember
          exact
            escapedDirection.trans fallbackDirection.symm
        · rw [
            retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_none_of_prefix_length_ne_one
              formula baseIndex literalIndex choiceLookup prefixLength]
    | some choice =>
        rw [
          retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_some
            formula baseIndex literalIndex choice
            (rawClause.scale
              retainedAngularFanSourceClearanceFactor)
            sourceLiteral choiceLookup scaledClauseLookup literalLookup,
          fallbackOccurrence]
        have directDirection :
            AxisDirection.polylineLastDirection
                (retainedFinalCoordinatedDirectOccurrenceRoute
                  formula choice
                  (rawClause.scale
                    retainedAngularFanSourceClearanceFactor)
                  sourceLiteral baseIndex literalIndex) =
              AxisDirection.polylineLastDirection
                (angularOccurrenceSuffix
                  scaledPlacement
                  (angularOccurrenceOrder
                    scaledSource.erase scaledRoutes)
                  (rawClause.scale
                    retainedAngularFanSourceClearanceFactor)
                  sourceLiteral baseIndex literalIndex) := by
          simpa [scaledSource, scaledPlacement, scaledRoutes,
            finalCoordinatedSource,
            finalCoordinatedPlacement,
            finalCoordinatedSourceRoutes] using
            retainedFinalCoordinatedDirectOccurrenceRoute_lastDirection
              formula sourceLocal sourceWidth sourceOccurrences
              sourceClausesNonempty choice
              rawTaggedClauseMember rawLiteralMember
              choiceLookup
        exact
          directDirection.trans fallbackDirection.symm
  · have sourceIndexGe :
        scaledSource.clauses.length ≤ baseIndex := by
      simpa [PeriodicEightOccurrenceSplitPositioned.occurrenceClauses,
        scaledSource] using occurrenceIndex
    have scaledClauseLookup :
        finalCoordinatedScaledClause?
            formula baseIndex = none := by
      apply
        finalCoordinatedScaledClause?_eq_none_of_length_le_for_route_order
      simpa [scaledSource, finalCoordinatedSource] using sourceIndexGe
    rw [
      retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_clause_none
        formula baseIndex literalIndex scaledClauseLookup]

/-- The final coordinated retained fixed-eight route family follows
syntactic occurrence order clockwise at every degree-three split variable. -/
theorem
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_variableRoutesInOccurrenceOrder
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ []) :
    PositionedPeriodicCNF.VariableRoutesInOccurrenceOrder
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        formula)
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula) := by
  apply
    PositionedPeriodicCNF.VariableRoutesInOccurrenceOrder.of_memberwise_lastDirection_eq
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes_variableRoutesInOccurrenceOrder
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
  intro clause clauseIndex clauseMember
    literal literalIndex literalMember
  exact
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_lastDirection_eq_fallback
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember

end PeriodicOrthocrossing
end LeanTrominoes
