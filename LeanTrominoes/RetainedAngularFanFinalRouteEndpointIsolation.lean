/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalOccurrenceEndpointIsolation
import LeanTrominoes.RetainedAngularFanFinalCycleSeparation
import LeanTrominoes.RetainedAngularFanFinalCoordinatedRouteFamily

/-!
# Endpoint isolation for the final coordinated fixed-eight routes

Copied-source routes use the endpoint-isolation certificate of the final
three-way route selector.  Appended implication-cycle routes are simple, so
their positively scaled orthogonal lattice paths have the same certificate.
This combines the two cases at the public formula-indexed interface.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

set_option maxHeartbeats 2000000

/-- Every genuine route in the final coordinated fixed-eight family visits
its variable endpoint only at the final unit-subdivided point. -/
theorem
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_lastNotInDropLast
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
    AxisDirection.LastNotInDropLast
      (AxisDirection.unitSubdividePolyline
        (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
          formula clauseIndex literalIndex)) := by
  rw [retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula,
    retainedAngularFanSourceScaledRefinedFormula,
    retainedAngularFanRefinedFormula,
    PositionedPeriodicCNF.scale_clauses,
    List.zipIdx_map] at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨taggedClause, taggedClauseMember, taggedClauseEqual⟩
  rcases taggedClause with ⟨baseClause, baseIndex⟩
  have clauseIndexEqual : baseIndex = clauseIndex :=
    congrArg Prod.snd taggedClauseEqual
  have scaledClauseEqual :
      baseClause.scale retainedTerminalFanRoutingRefinement = clause :=
    congrArg Prod.fst taggedClauseEqual
  subst clauseIndex
  subst clause
  have baseLiteralMember :
      (literal, literalIndex) ∈ baseClause.literals.zipIdx := by
    simpa using literalMember
  have finalClauseMember :
      (baseClause.scale retainedTerminalFanRoutingRefinement, baseIndex) ∈
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
          formula).clauses.zipIdx := by
    rw [retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula,
      retainedAngularFanSourceScaledRefinedFormula,
      retainedAngularFanRefinedFormula,
      PositionedPeriodicCNF.scale_clauses,
      List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(baseClause, baseIndex), taggedClauseMember, rfl⟩
  have finalLiteralMember :
      (literal, literalIndex) ∈
        (baseClause.scale
          retainedTerminalFanRoutingRefinement).literals.zipIdx := by
    simpa using baseLiteralMember
  let source :=
    (finalCoordinatedSource formula).scale
      retainedAngularFanSourceClearanceFactor
  let placement :=
    (finalCoordinatedPlacement formula).scale
      retainedAngularFanSourceClearanceFactor
  let routes :=
    PositionedPeriodicCNF.scaleIncidenceRoutes
      retainedAngularFanSourceClearanceFactor
      (finalCoordinatedSourceRoutes formula)
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
    rcases
        occurrenceMetadata_of_members
          source occurrencePorts copiedClauseMember
          baseLiteralMember with
      ⟨metadata, sourceLiteral,
        _metadataClauseEqual, metadataIndex,
        sourceClauseMember, sourceLiteralMember,
        _copiedLiteralEqual⟩
    have sourceClauseMemberAt :
        (metadata.sourceClause, baseIndex) ∈
          source.clauses.zipIdx := by
      simpa [metadataIndex] using sourceClauseMember
    dsimp only [source] at sourceClauseMemberAt
    rw [PositionedPeriodicCNF.scale_clauses,
      List.zipIdx_map] at sourceClauseMemberAt
    rcases List.mem_map.mp sourceClauseMemberAt with
      ⟨rawTaggedClause, rawTaggedClauseMember,
        rawTaggedClauseEqual⟩
    rcases rawTaggedClause with ⟨rawClause, rawIndex⟩
    have rawIndexEqual : rawIndex = baseIndex :=
      congrArg Prod.snd rawTaggedClauseEqual
    have rawScaledClauseEqual :
        rawClause.scale retainedAngularFanSourceClearanceFactor =
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
    exact
      retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_source_lastNotInDropLast
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty rawTaggedClauseMember rawLiteralMember
  · have cycleClauseMember :=
      cycleClauseMember_of_formula_member
        source placement occurrencePorts taggedClauseMember
        (by simpa [occurrencePorts] using occurrenceIndex)
    have clauseIndexDecomposition :
        baseIndex =
          (PeriodicEightOccurrenceSplitPositioned.occurrenceClauses
            source occurrencePorts).length +
            (baseIndex -
              (PeriodicEightOccurrenceSplitPositioned.occurrenceClauses
                source occurrencePorts).length) := by
      omega
    apply AxisDirection.lastNotInDropLast_unitSubdividePolyline_of_simple
    · exact
        (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_valid
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty finalClauseMember
          finalLiteralMember).2.2
    · rw [clauseIndexDecomposition]
      exact
        retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_cycleRoute_isSimple
          formula cycleClauseMember baseLiteralMember

end PeriodicOrthocrossing
end LeanTrominoes
