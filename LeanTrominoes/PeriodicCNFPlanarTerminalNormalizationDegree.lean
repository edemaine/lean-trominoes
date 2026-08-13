/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarComponentNormalizationDegree

/-!
# Degree bounds for normalized planar SAT terminals

This module recovers represented route occurrences from normalized terminal
attachments.  An active source-clause or target-arm attachment excludes bend
clauses at the same terminal; without an attachment, the bend family
contributes at most two occurrences.  Together with the six-occurrence
complete-carrier bound, every terminal prototype therefore has degree at most
eight.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

theorem normalizedRoutedClause_terminal_mem_exists_occurrence
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (indexed : IndexedGridSegment)
    (targetMem :
      .terminal indexed .start ∈
        (deduplicatedNormalizedRoutedClauseFormula
          formula).variableOccurrences) :
    ∃ occurrence : CNFRouteOccurrence Variable,
      occurrence ∈ drawingCNFRouteOccurrences formula ∧
      (occurrence.sourceTerminal formula).indexed = indexed := by
  unfold deduplicatedNormalizedRoutedClauseFormula
    PeriodicCNF.variableOccurrences at targetMem
  rcases List.mem_flatMap.mp targetMem with
    ⟨clause, clauseMem, terminalMem⟩
  have clauseRaw :
      clause ∈ normalizedRoutedClauseClauses formula :=
    List.mem_dedup.mp clauseMem
  rcases normalizedRoutedClause_mem_witness
    formula clauseRaw with
      ⟨site, _siteMem, clauseEq⟩
  rw [clauseEq] at terminalMem
  rcases List.mem_map.mp terminalMem with
    ⟨literal, literalMem, atomEq⟩
  rcases List.mem_map.mp literalMem with
    ⟨taggedIncidence, taggedIncidenceMem, literalEq⟩
  let occurrence : CNFRouteOccurrence Variable :=
    ⟨taggedIncidence.1, taggedIncidence.2, (0, 0)⟩
  have occurrenceMem :
      occurrence ∈ drawingCNFRouteOccurrences formula := by
    unfold occurrence drawingCNFRouteOccurrences
    apply List.mem_flatMap.mpr
    refine
      ⟨taggedIncidence,
        (List.mem_filter.mp taggedIncidenceMem).1, ?_⟩
    apply List.mem_map.mpr
    refine ⟨(0, 0), ?_, rfl⟩
    simp [IsNeighborTranslation]
  have indexedEq :
      (occurrence.sourceTerminal formula).indexed = indexed := by
    exact
      (PeriodicPlanarSATVariable.terminal.inj
        ((congrArg PeriodicLiteral.atom literalEq).trans
          atomEq)).1
  exact ⟨occurrence, occurrenceMem, indexedEq⟩

theorem
    deduplicatedNormalizedRoutedVariableFormula_terminal_mem_exists_occurrence
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (indexed : IndexedGridSegment)
    (targetMem :
      .terminal indexed .finish ∈
        (deduplicatedNormalizedRoutedVariableFormula
          formula).variableOccurrences) :
    ∃ occurrence : CNFRouteOccurrence Variable,
      occurrence ∈ drawingCNFRouteOccurrences formula ∧
      (occurrence.targetTerminal formula).indexed = indexed := by
  have targetCountPos :
      0 <
        (deduplicatedNormalizedRoutedVariableFormula
          formula).variableOccurrences.count
            (.terminal indexed .finish) :=
    List.count_pos_iff.mpr targetMem
  unfold deduplicatedNormalizedRoutedVariableFormula at targetCountPos
  rw [PeriodicEquality.deduplicatedNormalizedFormula_occurrence_count]
    at targetCountPos
  have endpointCountPos :
      0 <
        (PeriodicEquality.normalizedLinkEndpoints
          (deduplicatedNormalizedRoutedVariableLinks formula)).count
            (.terminal indexed .finish) := by
    unfold deduplicatedNormalizedRoutedVariableLinks
    omega
  have endpointMem :
      .terminal indexed .finish ∈
        PeriodicEquality.normalizedLinkEndpoints
          (deduplicatedNormalizedRoutedVariableLinks formula) :=
    List.count_pos_iff.mp endpointCountPos
  unfold PeriodicEquality.normalizedLinkEndpoints at endpointMem
  rcases List.mem_flatMap.mp endpointMem with
    ⟨link, linkMem, linkEndpointMem⟩
  have linkRaw :
      link ∈
        (drawingRoutedVariableLinks formula).map
          (PeriodicEquality.normalizeLink
            (normalizePlanarSATNode
              (PeriodicCNF.incidenceGraph formula))) :=
    List.mem_dedup.mp linkMem
  rcases List.mem_map.mp linkRaw with
    ⟨source, sourceMem, linkEq⟩
  rcases drawingRoutedVariableLink_witness
    formula sourceMem with
      ⟨site, occurrence, occurrenceMem, siteEq,
        sourceFirst, sourceSecond⟩
  subst link
  have normalized :=
    normalizeRoutedVariableLink_eq_of_witness
      formula siteEq sourceFirst sourceSecond
  rw [normalized] at linkEndpointMem
  have indexedEq :
      (occurrence.targetTerminal formula).indexed = indexed := by
    have reverseEq :
        indexed =
          (occurrence.targetTerminal formula).indexed := by
      simpa using linkEndpointMem
    exact reverseEq.symm
  exact ⟨occurrence, occurrenceMem, indexedEq⟩

theorem
    embeddedNormalizedRouteBendClauses_sourceTerminal_count_eq_zero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (occurrence : CNFRouteOccurrence Variable) :
    (PeriodicCNF.variableOccurrences
      ⟨(embeddedNormalizedRouteBendClauses
        formula).dedup⟩).count
          (.terminal
            (occurrence.sourceTerminal formula).indexed .start) = 0 := by
  unfold embeddedNormalizedRouteBendClauses
  rw [embeddedPeriodicCarrierClauses_dedup_terminal_count]
  exact
    deduplicatedNormalizedRouteBendFormula_sourceTerminal_count_eq_zero
      formula occurrence

theorem
    embeddedNormalizedRouteBendClauses_targetTerminal_count_eq_zero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMem :
      occurrence ∈ drawingCNFRouteOccurrences formula) :
    (PeriodicCNF.variableOccurrences
      ⟨(embeddedNormalizedRouteBendClauses
        formula).dedup⟩).count
          (.terminal
            (occurrence.targetTerminal formula).indexed .finish) = 0 := by
  unfold embeddedNormalizedRouteBendClauses
  rw [embeddedPeriodicCarrierClauses_dedup_terminal_count]
  exact
    deduplicatedNormalizedRouteBendFormula_targetTerminal_count_eq_zero
      formula occurrenceMem

theorem
    componentwiseDeduplicatedDrawingPeriodicPlanarSATFormula_terminal_count_le_eight
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (indexed : IndexedGridSegment)
    (endpoint : SegmentEnd) :
    (componentwiseDeduplicatedDrawingPeriodicPlanarSATFormula
      formula).variableOccurrences.count
        (.terminal indexed endpoint) ≤ 8 := by
  have crossoverZero :
      (PeriodicCNF.variableOccurrences
        ⟨(normalizedScopedDrawingCrossoverClauses
          formula).dedup⟩).count
            (.terminal indexed endpoint) = 0 :=
    normalizedScopedDrawingCrossoverClauses_terminal_count_eq_zero
      formula indexed endpoint
  have carrierLe :
      (PeriodicCNF.variableOccurrences
        ⟨(embeddedNormalizedCompleteCarrierClauses
          formula).dedup⟩).count
            (.terminal indexed endpoint) ≤ 6 :=
    embeddedNormalizedCompleteCarrierClauses_terminal_count_le_six'
      wellFormed degree isLocal indexed endpoint
  cases endpoint with
  | start =>
      have clauseLe :
          (PeriodicCNF.variableOccurrences
            ⟨(normalizedRoutedClauseClauses
              formula).dedup⟩).count
                (.terminal indexed .start) ≤ 1 := by
        exact
          deduplicatedNormalizedRoutedClauseFormula_terminal_count_le_one
            formula indexed
      have variableZero :
          (PeriodicCNF.variableOccurrences
            ⟨(PeriodicEquality.normalizedFormulaClauses
              (normalizePlanarSATNode
                (PeriodicCNF.incidenceGraph formula))
              (drawingRoutedVariableLinks formula)).dedup⟩).count
                (.terminal indexed .start) = 0 := by
        exact
          deduplicatedNormalizedRoutedVariableFormula_start_count_eq_zero
            formula indexed
      by_cases clauseMem :
          .terminal indexed .start ∈
            (deduplicatedNormalizedRoutedClauseFormula
              formula).variableOccurrences
      · rcases
          normalizedRoutedClause_terminal_mem_exists_occurrence
            formula indexed clauseMem with
              ⟨occurrence, occurrenceMem, indexedEq⟩
        have bendZero :
            (PeriodicCNF.variableOccurrences
              ⟨(embeddedNormalizedRouteBendClauses
                formula).dedup⟩).count
                  (.terminal indexed .start) = 0 := by
          rw [← indexedEq]
          exact
            embeddedNormalizedRouteBendClauses_sourceTerminal_count_eq_zero
              formula occurrence
        rw [
          componentwiseDeduplicatedDrawingPeriodicPlanarSATFormula_terminal_occurrence_count
            formula indexed .start,
          crossoverZero, bendZero, variableZero]
        omega
      · have clauseZero :
            (PeriodicCNF.variableOccurrences
              ⟨(normalizedRoutedClauseClauses
                formula).dedup⟩).count
                  (.terminal indexed .start) = 0 := by
          apply List.count_eq_zero_of_not_mem
          exact clauseMem
        have bendLe :
            (PeriodicCNF.variableOccurrences
              ⟨(embeddedNormalizedRouteBendClauses
                formula).dedup⟩).count
                  (.terminal indexed .start) ≤ 2 :=
          embeddedNormalizedRouteBendClauses_terminal_count_le_two
            formula indexed .start
        rw [
          componentwiseDeduplicatedDrawingPeriodicPlanarSATFormula_terminal_occurrence_count
            formula indexed .start,
          crossoverZero, clauseZero, variableZero]
        omega
  | finish =>
      have clauseZero :
          (PeriodicCNF.variableOccurrences
            ⟨(normalizedRoutedClauseClauses
              formula).dedup⟩).count
                (.terminal indexed .finish) = 0 := by
        exact
          deduplicatedNormalizedRoutedClauseFormula_finish_count_eq_zero
            formula indexed
      have variableLe :
          (PeriodicCNF.variableOccurrences
            ⟨(PeriodicEquality.normalizedFormulaClauses
              (normalizePlanarSATNode
                (PeriodicCNF.incidenceGraph formula))
              (drawingRoutedVariableLinks formula)).dedup⟩).count
                (.terminal indexed .finish) ≤ 2 := by
        exact
          deduplicatedNormalizedRoutedVariableFormula_terminal_count_le_two
            formula indexed
      by_cases variableMem :
          .terminal indexed .finish ∈
            (deduplicatedNormalizedRoutedVariableFormula
              formula).variableOccurrences
      · rcases
          deduplicatedNormalizedRoutedVariableFormula_terminal_mem_exists_occurrence
            formula indexed variableMem with
              ⟨occurrence, occurrenceMem, indexedEq⟩
        have bendZero :
            (PeriodicCNF.variableOccurrences
              ⟨(embeddedNormalizedRouteBendClauses
                formula).dedup⟩).count
                  (.terminal indexed .finish) = 0 := by
          rw [← indexedEq]
          exact
            embeddedNormalizedRouteBendClauses_targetTerminal_count_eq_zero
              formula occurrenceMem
        rw [
          componentwiseDeduplicatedDrawingPeriodicPlanarSATFormula_terminal_occurrence_count
            formula indexed .finish,
          crossoverZero, bendZero, clauseZero]
        omega
      · have variableZero :
            (PeriodicCNF.variableOccurrences
              ⟨(PeriodicEquality.normalizedFormulaClauses
                (normalizePlanarSATNode
                  (PeriodicCNF.incidenceGraph formula))
                (drawingRoutedVariableLinks formula)).dedup⟩).count
                  (.terminal indexed .finish) = 0 := by
          apply List.count_eq_zero_of_not_mem
          exact variableMem
        have bendLe :
            (PeriodicCNF.variableOccurrences
              ⟨(embeddedNormalizedRouteBendClauses
                formula).dedup⟩).count
                  (.terminal indexed .finish) ≤ 2 :=
          embeddedNormalizedRouteBendClauses_terminal_count_le_two
            formula indexed .finish
        rw [
          componentwiseDeduplicatedDrawingPeriodicPlanarSATFormula_terminal_occurrence_count
            formula indexed .finish,
          crossoverZero, clauseZero, variableZero]
        omega

end PeriodicOrthocrossing
end LeanTrominoes
