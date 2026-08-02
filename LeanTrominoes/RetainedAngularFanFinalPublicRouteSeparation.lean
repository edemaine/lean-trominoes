import LeanTrominoes.RetainedAngularFanFinalCrossClausePublicSeparation
import LeanTrominoes.RetainedAngularFanFinalCopiedSourceCycleSeparation
import LeanTrominoes.RetainedAngularFanFinalCycleSeparation

/-!
# Pairwise separation of the complete final route family

The final positioned formula scales a copied-source prefix followed by the
flattened Figure 7 implication cycles.  This file removes that presentation
bookkeeping.  It recovers source incidences through the occurrence-copy
metadata, recovers cycle incidences by subtracting the append boundary, and
dispatches the resulting four structural pairings to the completed public
separation theorems.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 2000000

/-- Remove the final factor-eight coordinate scaling from one genuine public
incidence while preserving its presentation indices and literal value. -/
private theorem finalCoordinatedIncidence_unscale
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
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
    let occurrencePorts :=
      occurrencePortsOfAngularOrder source.erase
        (angularOccurrenceOrder source.erase routes)
    ∃ baseClause,
      (baseClause, clauseIndex) ∈
        (PeriodicEightOccurrenceSplitPositioned.formula
          source placement occurrencePorts).clauses.zipIdx ∧
      (literal, literalIndex) ∈
        baseClause.literals.zipIdx := by
  dsimp only
  rw [retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula,
    retainedAngularFanSourceScaledRefinedFormula,
    retainedAngularFanRefinedFormula,
    PositionedPeriodicCNF.scale_clauses,
    List.zipIdx_map] at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨taggedClause, taggedClauseMember, taggedClauseEqual⟩
  rcases taggedClause with ⟨baseClause, baseIndex⟩
  have indexEqual : baseIndex = clauseIndex :=
    congrArg Prod.snd taggedClauseEqual
  have clauseEqual :
      baseClause.scale retainedTerminalFanRoutingRefinement = clause :=
    congrArg Prod.fst taggedClauseEqual
  subst baseIndex
  subst clause
  exact ⟨baseClause, taggedClauseMember, by simpa using literalMember⟩

/-- A copied-prefix incidence of the unscaled split formula comes from a
genuine incidence of the raw coordinated source at the same indices. -/
private theorem rawCoordinatedSourceIncidence_of_occurrence
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
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
      let occurrencePorts :=
        occurrencePortsOfAngularOrder source.erase
          (angularOccurrenceOrder source.erase routes)
      (clause, clauseIndex) ∈
        (PeriodicEightOccurrenceSplitPositioned.formula
          source placement occurrencePorts).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (occurrenceIndex :
      let source :=
        (finalCoordinatedSource formula).scale
          retainedAngularFanSourceClearanceFactor
      let routes :=
        PositionedPeriodicCNF.scaleIncidenceRoutes
          retainedAngularFanSourceClearanceFactor
          (finalCoordinatedSourceRoutes formula)
      let occurrencePorts :=
        occurrencePortsOfAngularOrder source.erase
          (angularOccurrenceOrder source.erase routes)
      clauseIndex <
        (occurrenceClauses source occurrencePorts).length) :
    ∃ sourceClause sourceLiteral,
      (sourceClause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx ∧
      (sourceLiteral, literalIndex) ∈
        sourceClause.literals.zipIdx := by
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
  let order := angularOccurrenceOrder source.erase routes
  let occurrencePorts :=
    occurrencePortsOfAngularOrder source.erase order
  have copiedClauseMember :=
    occurrenceClauseMember_of_formula_member
      source placement order
      (by simpa [source, placement, routes, order, occurrencePorts] using
        clauseMember)
      (by simpa [source, routes, order, occurrencePorts] using
        occurrenceIndex)
  rcases occurrenceMetadata_of_members
      source occurrencePorts copiedClauseMember literalMember with
    ⟨metadata, sourceLiteral, _metadataClauseEqual,
      metadataIndex, scaledSourceClauseMember,
      sourceLiteralMember, _literalEqual⟩
  have scaledSourceClauseMemberAt :
      (metadata.sourceClause, clauseIndex) ∈
        source.clauses.zipIdx := by
    simpa [metadataIndex] using scaledSourceClauseMember
  dsimp only [source] at scaledSourceClauseMemberAt
  rw [PositionedPeriodicCNF.scale_clauses,
    List.zipIdx_map] at scaledSourceClauseMemberAt
  rcases List.mem_map.mp scaledSourceClauseMemberAt with
    ⟨taggedSourceClause, sourceClauseMember,
      taggedSourceClauseEqual⟩
  rcases taggedSourceClause with
    ⟨sourceClause, sourceClauseIndex⟩
  have sourceClauseIndexEqual :
      sourceClauseIndex = clauseIndex :=
    congrArg Prod.snd taggedSourceClauseEqual
  have scaledSourceClauseEqual :
      sourceClause.scale retainedAngularFanSourceClearanceFactor =
        metadata.sourceClause :=
    congrArg Prod.fst taggedSourceClauseEqual
  subst sourceClauseIndex
  have rawLiteralMember :
      (sourceLiteral, literalIndex) ∈
        sourceClause.literals.zipIdx := by
    have scaledLiteralMember :
        (sourceLiteral, literalIndex) ∈
          (sourceClause.scale
            retainedAngularFanSourceClearanceFactor).literals.zipIdx := by
      rw [scaledSourceClauseEqual]
      exact sourceLiteralMember
    simpa using scaledLiteralMember
  exact
    ⟨sourceClause, sourceLiteral,
      sourceClauseMember, rawLiteralMember⟩

/-- Every pair of distinct genuine incidences in the complete final
coordinated fixed-eight route family avoids each other. -/
theorem
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_avoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {firstClause secondClause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
          formula).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
          formula).clauses.zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx)
    (incidencesDistinct :
      firstClauseIndex ≠ secondClauseIndex ∨
        firstLiteralIndex ≠ secondLiteralIndex) :
    RoutesAvoidEachOther
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula firstClauseIndex firstLiteralIndex)
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula secondClauseIndex secondLiteralIndex) := by
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
  let order := angularOccurrenceOrder source.erase routes
  let occurrencePorts :=
    occurrencePortsOfAngularOrder source.erase order
  let boundary := (occurrenceClauses source occurrencePorts).length
  rcases finalCoordinatedIncidence_unscale
      formula firstClauseMember firstLiteralMember with
    ⟨firstBaseClause, firstBaseClauseMember,
      firstBaseLiteralMember⟩
  rcases finalCoordinatedIncidence_unscale
      formula secondClauseMember secondLiteralMember with
    ⟨secondBaseClause, secondBaseClauseMember,
      secondBaseLiteralMember⟩
  by_cases firstOccurrence : firstClauseIndex < boundary
  · rcases rawCoordinatedSourceIncidence_of_occurrence
        formula
        (by simpa [source, placement, routes, order, occurrencePorts] using
          firstBaseClauseMember)
        firstBaseLiteralMember
        (by simpa [source, routes, order, occurrencePorts, boundary] using
          firstOccurrence) with
      ⟨firstSourceClause, firstSourceLiteral,
        firstSourceClauseMember, firstSourceLiteralMember⟩
    by_cases secondOccurrence : secondClauseIndex < boundary
    · rcases rawCoordinatedSourceIncidence_of_occurrence
          formula
          (by simpa [source, placement, routes, order, occurrencePorts] using
            secondBaseClauseMember)
          secondBaseLiteralMember
          (by simpa [source, routes, order, occurrencePorts, boundary] using
            secondOccurrence) with
        ⟨secondSourceClause, secondSourceLiteral,
          secondSourceClauseMember, secondSourceLiteralMember⟩
      exact
        retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_copiedSource_avoidEachOther
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty
          firstSourceClauseMember secondSourceClauseMember
          firstSourceLiteralMember secondSourceLiteralMember
          incidencesDistinct
    · have secondCycleClauseMember :=
        cycleClauseMember_of_formula_member
          source placement occurrencePorts
          (by simpa [source, placement, routes, order, occurrencePorts] using
            secondBaseClauseMember)
          (by simpa [boundary] using secondOccurrence)
      have secondDecomposition :
          secondClauseIndex =
            boundary + (secondClauseIndex - boundary) := by
        omega
      rw [secondDecomposition]
      simpa only [source, placement, routes, order, occurrencePorts,
        boundary] using
        retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_copiedSource_avoids_cycleRoute
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty
          firstSourceClauseMember firstSourceLiteralMember
          secondCycleClauseMember secondBaseLiteralMember
  · have firstCycleClauseMember :=
      cycleClauseMember_of_formula_member
        source placement occurrencePorts
        (by simpa [source, placement, routes, order, occurrencePorts] using
          firstBaseClauseMember)
        (by simpa [boundary] using firstOccurrence)
    have firstDecomposition :
        firstClauseIndex =
          boundary + (firstClauseIndex - boundary) := by
      omega
    by_cases secondOccurrence : secondClauseIndex < boundary
    · rcases rawCoordinatedSourceIncidence_of_occurrence
          formula
          (by simpa [source, placement, routes, order, occurrencePorts] using
            secondBaseClauseMember)
          secondBaseLiteralMember
          (by simpa [source, routes, order, occurrencePorts, boundary] using
            secondOccurrence) with
        ⟨secondSourceClause, secondSourceLiteral,
          secondSourceClauseMember, secondSourceLiteralMember⟩
      apply routesAvoidEachOther_comm
      rw [firstDecomposition]
      simpa only [source, placement, routes, order, occurrencePorts,
        boundary] using
        retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_copiedSource_avoids_cycleRoute
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty
          secondSourceClauseMember secondSourceLiteralMember
          firstCycleClauseMember firstBaseLiteralMember
    · have secondCycleClauseMember :=
        cycleClauseMember_of_formula_member
          source placement occurrencePorts
          (by simpa [source, placement, routes, order, occurrencePorts] using
            secondBaseClauseMember)
          (by simpa [boundary] using secondOccurrence)
      have secondDecomposition :
          secondClauseIndex =
            boundary + (secondClauseIndex - boundary) := by
        omega
      have cycleIncidencesDistinct :
          firstClauseIndex - boundary ≠
              secondClauseIndex - boundary ∨
            firstLiteralIndex ≠ secondLiteralIndex := by
        rcases incidencesDistinct with
          clauseIndicesDifferent | literalIndicesDifferent
        · left
          intro cycleIndicesEqual
          apply clauseIndicesDifferent
          omega
        · exact Or.inr literalIndicesDifferent
      rw [firstDecomposition, secondDecomposition]
      simpa only [source, placement, routes, order, occurrencePorts,
        boundary] using
        retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_cycleRoutes_avoidEachOther
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty
          firstCycleClauseMember secondCycleClauseMember
          firstBaseLiteralMember secondBaseLiteralMember
          cycleIncidencesDistinct

end PeriodicOrthocrossing
end LeanTrominoes
