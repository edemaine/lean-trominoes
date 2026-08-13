/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarNormalizationComponents
import LeanTrominoes.PeriodicCNFPlanarCrossoverNormalizationDegree

/-!
# Degree bounds for normalized planar SAT components

This module separates terminal and central-atom prototypes from crossover
clauses, transfers carrier clause counts through the full planar SAT
embedding, removes the indexed-segment membership side condition, and proves
the componentwise central-atom bound.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

theorem normalizedScopedDrawingCrossoverClauses_eq_normalized_sites
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    normalizedScopedDrawingCrossoverClauses formula =
      (orientedCrossingHalo
        (PeriodicCNF.incidenceGraph formula)).flatMap fun crossing =>
          normalizedCrossoverClausesAt
            (Variable := Variable)
            (crossing.periodNormalize
              (PeriodicCNF.incidenceGraph formula)) := by
  unfold normalizedScopedDrawingCrossoverClauses
    drawingCarrierNodeCrossoverFormula
    crossoverFamily scopedCrossoverInstance
    instantiateFormula
  simp only [List.map_flatMap]
  apply List.flatMap_congr
  intro crossing _crossingMem
  unfold normalizedCrossoverClausesAt
  simp only [List.map_map]
  apply List.map_congr_left
  intro clause _clauseMem
  simpa [Function.comp_def] using
    normalizedCrossoverClauseAt_eq formula crossing clause

theorem normalizedScopedDrawingCrossoverClauses_dedup_subperm_canonical
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal) :
    List.Subperm
      (normalizedScopedDrawingCrossoverClauses formula).dedup
      (canonicalNormalizedCrossoverClauses
        (Variable := Variable)
        (PeriodicCNF.incidenceGraph formula)) := by
  apply (List.nodup_dedup _).subperm
  intro clause clauseMem
  have clauseRaw := List.mem_dedup.mp clauseMem
  rw [normalizedScopedDrawingCrossoverClauses_eq_normalized_sites]
    at clauseRaw
  rcases List.mem_flatMap.mp clauseRaw with
    ⟨crossing, crossingMem, clauseMem⟩
  unfold canonicalNormalizedCrossoverClauses
  apply List.mem_flatMap.mpr
  exact
    ⟨crossing.periodNormalize
        (PeriodicCNF.incidenceGraph formula),
      periodNormalize_mem_orientedCrossings
        wellFormed degree isLocal crossingMem,
      clauseMem⟩

theorem normalizedScopedDrawingCrossoverClauses_boundary_count_le_two
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (boundary : CrossingBoundary) :
    (PeriodicCNF.variableOccurrences
      ⟨(normalizedScopedDrawingCrossoverClauses
        formula).dedup⟩).count (.boundary boundary) ≤ 2 := by
  have clauseSubperm :
      List.Subperm
        (normalizedScopedDrawingCrossoverClauses formula).dedup
        (canonicalNormalizedCrossoverClauses
          (Variable := Variable)
          (PeriodicCNF.incidenceGraph formula)) :=
    normalizedScopedDrawingCrossoverClauses_dedup_subperm_canonical
      wellFormed degree isLocal
  have occurrenceLe :
      (PeriodicCNF.variableOccurrences
        ⟨(normalizedScopedDrawingCrossoverClauses
          formula).dedup⟩).count (.boundary boundary) ≤
        (PeriodicCNF.variableOccurrences
          ⟨canonicalNormalizedCrossoverClauses
            (Variable := Variable)
            (PeriodicCNF.incidenceGraph formula)⟩).count
              (.boundary boundary) := by
    unfold PeriodicCNF.variableOccurrences
    rcases clauseSubperm with
      ⟨middle, middlePerm, middleSublist⟩
    have occurrenceSubperm :
        List.Subperm
          ((normalizedScopedDrawingCrossoverClauses
            formula).dedup.flatMap fun clause =>
              clause.map PeriodicLiteral.atom)
          ((canonicalNormalizedCrossoverClauses
            (Variable := Variable)
            (PeriodicCNF.incidenceGraph formula)).flatMap fun clause =>
              clause.map PeriodicLiteral.atom) :=
      ⟨middle.flatMap fun clause =>
          clause.map PeriodicLiteral.atom,
        middlePerm.flatMap fun clause _ =>
          List.Perm.refl
            (clause.map PeriodicLiteral.atom),
        middleSublist.flatMap fun clause =>
          clause.map PeriodicLiteral.atom⟩
    exact occurrenceSubperm.count_le (.boundary boundary)
  exact occurrenceLe.trans
    (canonicalNormalizedCrossoverClauses_boundary_count_le_two
      (Variable := Variable)
      (PeriodicCNF.incidenceGraph formula) boundary)

theorem normalizedScopedDrawingCrossoverClauses_internal_count_le_eight
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (internal : CrossingRecord × CrossoverInternal) :
    (PeriodicCNF.variableOccurrences
      ⟨(normalizedScopedDrawingCrossoverClauses
        formula).dedup⟩).count
          (.crossoverInternal internal) ≤ 8 := by
  have clauseSubperm :
      List.Subperm
        (normalizedScopedDrawingCrossoverClauses formula).dedup
        (canonicalNormalizedCrossoverClauses
          (Variable := Variable)
          (PeriodicCNF.incidenceGraph formula)) :=
    normalizedScopedDrawingCrossoverClauses_dedup_subperm_canonical
      wellFormed degree isLocal
  have occurrenceLe :
      (PeriodicCNF.variableOccurrences
        ⟨(normalizedScopedDrawingCrossoverClauses
          formula).dedup⟩).count
            (.crossoverInternal internal) ≤
        (PeriodicCNF.variableOccurrences
          ⟨canonicalNormalizedCrossoverClauses
            (Variable := Variable)
            (PeriodicCNF.incidenceGraph formula)⟩).count
              (.crossoverInternal internal) := by
    unfold PeriodicCNF.variableOccurrences
    rcases clauseSubperm with
      ⟨middle, middlePerm, middleSublist⟩
    have occurrenceSubperm :
        List.Subperm
          ((normalizedScopedDrawingCrossoverClauses
            formula).dedup.flatMap fun clause =>
              clause.map PeriodicLiteral.atom)
          ((canonicalNormalizedCrossoverClauses
            (Variable := Variable)
            (PeriodicCNF.incidenceGraph formula)).flatMap fun clause =>
              clause.map PeriodicLiteral.atom) :=
      ⟨middle.flatMap fun clause =>
          clause.map PeriodicLiteral.atom,
        middlePerm.flatMap fun clause _ =>
          List.Perm.refl
            (clause.map PeriodicLiteral.atom),
        middleSublist.flatMap fun clause =>
          clause.map PeriodicLiteral.atom⟩
    exact occurrenceSubperm.count_le
      (.crossoverInternal internal)
  exact occurrenceLe.trans
    (canonicalNormalizedCrossoverClauses_occurrencesAtMostEight
      (Variable := Variable)
      (PeriodicCNF.incidenceGraph formula)
      (.crossoverInternal internal))

theorem normalizedScopedDrawingCrossoverClauses_terminal_count_eq_zero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (indexed : IndexedGridSegment) (endpoint : SegmentEnd) :
    (PeriodicCNF.variableOccurrences
      ⟨(normalizedScopedDrawingCrossoverClauses
        formula).dedup⟩).count
          (.terminal indexed endpoint) = 0 := by
  unfold PeriodicCNF.variableOccurrences
  apply List.count_eq_zero_of_not_mem
  intro terminalMem
  rcases List.mem_flatMap.mp terminalMem with
    ⟨clause, clauseMem, terminalMem⟩
  have clauseRaw :=
    List.mem_dedup.mp clauseMem
  rcases List.mem_map.mp clauseRaw with
    ⟨periodicClause, periodicClauseMem, clauseEq⟩
  rcases List.mem_map.mp periodicClauseMem with
    ⟨embeddedClause, embeddedClauseMem, periodicClauseEq⟩
  rcases List.mem_map.mp embeddedClauseMem with
    ⟨sourceClause, sourceClauseMem, embeddedClauseEq⟩
  subst clause
  subst periodicClause
  subst embeddedClause
  rw [PeriodicClause.anchorNormalize_map_atom] at terminalMem
  rcases List.mem_map.mp terminalMem with
    ⟨literal, literalMem, atomEq⟩
  rcases List.mem_map.mp literalMem with
    ⟨sourceLiteral, sourceLiteralMem, literalEq⟩
  change sourceLiteral ∈
    sourceClause.literals.map
      (fun literal =>
        (planarSATCoreVariableMap literal.1,
          literal.2)) at sourceLiteralMem
  rcases List.mem_map.mp sourceLiteralMem with
    ⟨coreLiteral, coreLiteralMem, sourceLiteralEq⟩
  subst sourceLiteral
  have sourceAtomEq :
      (normalizePlanarSATVariable
        formula (planarSATCoreVariableMap coreLiteral.1)).1 =
          .terminal indexed endpoint :=
    (congrArg PeriodicLiteral.atom literalEq).trans atomEq
  rcases coreLiteral with ⟨sourceVariable, polarity⟩
  cases sourceVariable with
  | inl carrier =>
      have carrierEq :
          ∃ terminal,
            carrier = .terminal terminal := by
        cases carrier with
        | terminal terminal =>
            exact ⟨terminal, rfl⟩
        | boundary boundary =>
            simp [planarSATCoreVariableMap,
              normalizePlanarSATVariable] at sourceAtomEq
      rcases carrierEq with ⟨terminal, rfl⟩
      have sourceOccurrence :
          (.inl (.terminal terminal) :
            Sum CarrierNode
              (CrossingRecord × CrossoverInternal)) ∈
            embeddedVariableOccurrences
              (drawingCarrierNodeCrossoverFormula
                (PeriodicCNF.incidenceGraph formula)) := by
        unfold embeddedVariableOccurrences
        exact List.mem_flatMap.mpr
          ⟨sourceClause, sourceClauseMem,
            List.mem_map.mpr
              ⟨(.inl (.terminal terminal), polarity),
                coreLiteralMem, rfl⟩⟩
      have zero :=
        drawingCarrierNodeCrossoverFormula_terminal_count_eq_zero
          (PeriodicCNF.incidenceGraph formula) terminal
      exact
        (@List.count_eq_zero
          (Sum CarrierNode
            (CrossingRecord × CrossoverInternal))
          instBEqOfDecidableEq
          (by infer_instance)
          (.inl (.terminal terminal))
          (embeddedVariableOccurrences
            (drawingCarrierNodeCrossoverFormula
              (PeriodicCNF.incidenceGraph formula)))).mp
          zero sourceOccurrence
  | inr internal =>
      simp [planarSATCoreVariableMap,
        normalizePlanarSATVariable] at sourceAtomEq

theorem normalizedScopedDrawingCrossoverClauses_atom_count_eq_zero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (atom : Variable) :
    (PeriodicCNF.variableOccurrences
      ⟨(normalizedScopedDrawingCrossoverClauses
        formula).dedup⟩).count (.atom atom) = 0 := by
  unfold PeriodicCNF.variableOccurrences
  apply List.count_eq_zero_of_not_mem
  intro atomMem
  rcases List.mem_flatMap.mp atomMem with
    ⟨clause, clauseMem, atomMem⟩
  have clauseRaw :=
    List.mem_dedup.mp clauseMem
  rcases List.mem_map.mp clauseRaw with
    ⟨periodicClause, periodicClauseMem, clauseEq⟩
  rcases List.mem_map.mp periodicClauseMem with
    ⟨embeddedClause, embeddedClauseMem, periodicClauseEq⟩
  rcases List.mem_map.mp embeddedClauseMem with
    ⟨sourceClause, sourceClauseMem, embeddedClauseEq⟩
  subst clause
  subst periodicClause
  subst embeddedClause
  rw [PeriodicClause.anchorNormalize_map_atom] at atomMem
  rcases List.mem_map.mp atomMem with
    ⟨literal, literalMem, atomEq⟩
  rcases List.mem_map.mp literalMem with
    ⟨sourceLiteral, sourceLiteralMem, literalEq⟩
  change sourceLiteral ∈
    sourceClause.literals.map
      (fun literal =>
        (planarSATCoreVariableMap literal.1,
          literal.2)) at sourceLiteralMem
  rcases List.mem_map.mp sourceLiteralMem with
    ⟨coreLiteral, coreLiteralMem, sourceLiteralEq⟩
  subst sourceLiteral
  have impossible :
      (normalizePlanarSATVariable
        formula (planarSATCoreVariableMap coreLiteral.1)).1 =
          .atom atom :=
    (congrArg PeriodicLiteral.atom literalEq).trans atomEq
  rcases coreLiteral with ⟨sourceVariable, polarity⟩
  cases sourceVariable with
  | inl carrier =>
      cases carrier <;>
        simp [planarSATCoreVariableMap,
          normalizePlanarSATVariable] at impossible
  | inr internal =>
      simp [planarSATCoreVariableMap,
        normalizePlanarSATVariable] at impossible

theorem embeddedPeriodicCarrierClauses_dedup_terminal_count
    {Variable : Type*} [DecidableEq Variable]
    (clauses : List (PeriodicClause PeriodicCarrierNode))
    (indexed : IndexedGridSegment) (endpoint : SegmentEnd) :
    (PeriodicCNF.variableOccurrences
      ⟨(clauses.map
        (@embedPeriodicCarrierClause Variable)).dedup⟩).count
          (.terminal indexed endpoint) =
      (PeriodicCNF.variableOccurrences
        ⟨clauses.dedup⟩).count
          (.terminal indexed endpoint) := by
  rw [List.dedup_map_of_injective
    (@embedPeriodicCarrierClause_injective Variable)]
  change
    (embedPeriodicCarrierFormula
      (Variable := Variable)
      ⟨clauses.dedup⟩).variableOccurrences.count
        (.terminal indexed endpoint) =
      (PeriodicCNF.variableOccurrences
        ⟨clauses.dedup⟩).count
          (.terminal indexed endpoint)
  exact embedPeriodicCarrierFormula_terminal_count
    ⟨clauses.dedup⟩ indexed endpoint

theorem embeddedPeriodicCarrierClauses_dedup_boundary_count
    {Variable : Type*} [DecidableEq Variable]
    (clauses : List (PeriodicClause PeriodicCarrierNode))
    (boundary : CrossingBoundary) :
    (PeriodicCNF.variableOccurrences
      ⟨(clauses.map
        (@embedPeriodicCarrierClause Variable)).dedup⟩).count
          (.boundary boundary) =
      (PeriodicCNF.variableOccurrences
        ⟨clauses.dedup⟩).count
          (.boundary boundary) := by
  rw [List.dedup_map_of_injective
    (@embedPeriodicCarrierClause_injective Variable)]
  change
    (embedPeriodicCarrierFormula
      (Variable := Variable)
      ⟨clauses.dedup⟩).variableOccurrences.count
        (.boundary boundary) =
      (PeriodicCNF.variableOccurrences
        ⟨clauses.dedup⟩).count
          (.boundary boundary)
  exact embedPeriodicCarrierFormula_boundary_count
    ⟨clauses.dedup⟩ boundary

theorem PeriodicEquality.normalizedFormulaClauses_dedup_count_eq_zero_of_endpoints
    {Source Target : Type*}
    [DecidableEq Source] [DecidableEq Target]
    (normalize : Source → Target × Cell)
    (links : List (EqualityLink Source))
    (target : Target)
    (absent :
      ∀ link ∈ links,
        (normalize link.first).1 ≠ target ∧
          (normalize link.second).1 ≠ target) :
    (PeriodicCNF.variableOccurrences
      ⟨(PeriodicEquality.normalizedFormulaClauses
        normalize links).dedup⟩).count target = 0 := by
  change
    (PeriodicEquality.deduplicatedNormalizedFormula
      normalize links).variableOccurrences.count target = 0
  rw [PeriodicEquality.deduplicatedNormalizedFormula_occurrence_count]
  apply Nat.mul_eq_zero.mpr
  right
  apply List.count_eq_zero_of_not_mem
  intro targetMem
  rcases List.mem_flatMap.mp targetMem with
    ⟨link, linkMem, endpointMem⟩
  have linkRaw :
      link ∈
        links.map (PeriodicEquality.normalizeLink normalize) :=
    List.mem_dedup.mp linkMem
  rcases List.mem_map.mp linkRaw with
    ⟨source, sourceMem, sourceEq⟩
  subst link
  have incident :
      (normalize source.first).1 = target ∨
        (normalize source.second).1 = target := by
    simpa [PeriodicEquality.normalizedLinkEndpoints,
      PeriodicEquality.normalizeLink, eq_comm] using endpointMem
  exact incident.elim
    (absent source sourceMem).1
    (absent source sourceMem).2

theorem
    embeddedNormalizedCompleteCarrierClauses_terminal_count_le_six
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {indexed : IndexedGridSegment}
    (indexedMem :
      indexed ∈
        (drawing
          (PeriodicCNF.incidenceGraph formula)).indexedSegments)
    (endpoint : SegmentEnd) :
    (PeriodicCNF.variableOccurrences
      ⟨(embeddedNormalizedCompleteCarrierClauses
        formula).dedup⟩).count
          (.terminal indexed endpoint) ≤ 6 := by
  unfold embeddedNormalizedCompleteCarrierClauses
  rw [embeddedPeriodicCarrierClauses_dedup_terminal_count]
  exact
    deduplicatedNormalizedCompleteCarrierFormula_terminal_count_le_six
      wellFormed degree isLocal indexedMem endpoint

theorem embeddedNormalizedRouteBendClauses_terminal_count_le_two
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (indexed : IndexedGridSegment) (endpoint : SegmentEnd) :
    (PeriodicCNF.variableOccurrences
      ⟨(embeddedNormalizedRouteBendClauses
        formula).dedup⟩).count
          (.terminal indexed endpoint) ≤ 2 := by
  unfold embeddedNormalizedRouteBendClauses
  rw [embeddedPeriodicCarrierClauses_dedup_terminal_count]
  exact
    deduplicatedNormalizedRouteBendFormula_terminal_count_le_two
      (PeriodicCNF.incidenceGraph formula) indexed endpoint

theorem
    embeddedNormalizedCompleteCarrierClauses_boundary_count_le_four
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (boundary : CrossingBoundary) :
    (PeriodicCNF.variableOccurrences
      ⟨(embeddedNormalizedCompleteCarrierClauses
        formula).dedup⟩).count
          (.boundary boundary) ≤ 4 := by
  unfold embeddedNormalizedCompleteCarrierClauses
  rw [embeddedPeriodicCarrierClauses_dedup_boundary_count]
  exact
    deduplicatedNormalizedCompleteCarrierFormula_boundary_count_le_four
      (PeriodicCNF.incidenceGraph formula) boundary

theorem
    embeddedNormalizedRouteBendClauses_boundary_count_eq_zero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (boundary : CrossingBoundary) :
    (PeriodicCNF.variableOccurrences
      ⟨(embeddedNormalizedRouteBendClauses
        formula).dedup⟩).count
          (.boundary boundary) = 0 := by
  unfold embeddedNormalizedRouteBendClauses
  rw [embeddedPeriodicCarrierClauses_dedup_boundary_count]
  apply
    PeriodicEquality.normalizedFormulaClauses_dedup_count_eq_zero_of_endpoints
  intro link linkMem
  rcases List.mem_map.mp linkMem with
    ⟨routeBend, _routeBendMem, linkEq⟩
  subst link
  simp [RouteBend.equalityLink, normalizeCarrierNode]

theorem
    deduplicatedNormalizedCompleteCarrierFormula_terminal_count_eq_zero_of_not_mem
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (indexed : IndexedGridSegment)
    (indexedNotMem :
      indexed ∉ (drawing graph).indexedSegments)
    (endpoint : SegmentEnd) :
    (deduplicatedNormalizedCompleteCarrierFormula
      graph).variableOccurrences.count
        (.terminal indexed endpoint) = 0 := by
  unfold deduplicatedNormalizedCompleteCarrierFormula
  rw [PeriodicEquality.deduplicatedNormalizedFormula_occurrence_count]
  apply Nat.mul_eq_zero.mpr
  right
  apply List.count_eq_zero_of_not_mem
  intro terminalMem
  rcases List.mem_flatMap.mp terminalMem with
    ⟨link, linkMem, endpointMem⟩
  have linkRaw :
      link ∈
        (drawingCompleteCarrierLinks graph).map
          (PeriodicEquality.normalizeLink
            (normalizeCarrierNode graph)) :=
    List.mem_dedup.mp linkMem
  rcases List.mem_map.mp linkRaw with
    ⟨source, sourceMem, sourceEq⟩
  subst link
  have incident :
      (PeriodicEquality.normalizeLink
          (normalizeCarrierNode graph) source).first =
            .terminal indexed endpoint ∨
        (PeriodicEquality.normalizeLink
          (normalizeCarrierNode graph) source).second =
            .terminal indexed endpoint := by
    simpa [PeriodicEquality.normalizedLinkEndpoints,
      eq_comm] using endpointMem
  rcases (normalizedLink_incident_terminal_iff
    graph source indexed endpoint).mp incident with
      ⟨translate, sourceIncident⟩
  have sourceTerminalMem :
      (⟨indexed, translate, endpoint⟩ :
        SegmentTerminal) ∈
          drawingSegmentTerminals graph :=
    drawingCompleteCarrierLink_terminal_mem
      graph sourceMem sourceIncident
  exact indexedNotMem
    (drawingSegmentTerminal_indexed_mem
      graph sourceTerminalMem).1

theorem
    embeddedNormalizedCompleteCarrierClauses_terminal_count_le_six'
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
    (PeriodicCNF.variableOccurrences
      ⟨(embeddedNormalizedCompleteCarrierClauses
        formula).dedup⟩).count
          (.terminal indexed endpoint) ≤ 6 := by
  by_cases indexedMem :
      indexed ∈
        (drawing
          (PeriodicCNF.incidenceGraph formula)).indexedSegments
  · exact
      embeddedNormalizedCompleteCarrierClauses_terminal_count_le_six
        wellFormed degree isLocal indexedMem endpoint
  · unfold embeddedNormalizedCompleteCarrierClauses
    rw [embeddedPeriodicCarrierClauses_dedup_terminal_count]
    change
      (deduplicatedNormalizedCompleteCarrierFormula
        (PeriodicCNF.incidenceGraph formula)).variableOccurrences.count
          (.terminal indexed endpoint) ≤ 6
    rw [
      deduplicatedNormalizedCompleteCarrierFormula_terminal_count_eq_zero_of_not_mem
        (PeriodicCNF.incidenceGraph formula)
        indexed indexedMem endpoint]
    omega

theorem embeddedPeriodicCarrierClauses_dedup_atom_count_eq_zero
    {Variable : Type*} [DecidableEq Variable]
    (clauses : List (PeriodicClause PeriodicCarrierNode))
    (atom : Variable) :
    (PeriodicCNF.variableOccurrences
      ⟨(clauses.map
        (@embedPeriodicCarrierClause Variable)).dedup⟩).count
          (.atom atom) = 0 := by
  rw [List.dedup_map_of_injective
    (@embedPeriodicCarrierClause_injective Variable)]
  change
    (embedPeriodicCarrierFormula
      (Variable := Variable)
      ⟨clauses.dedup⟩).variableOccurrences.count
        (.atom atom) = 0
  apply List.count_eq_zero_of_not_mem
  rw [embedPeriodicCarrierFormula_variableOccurrences]
  intro atomMem
  rcases List.mem_map.mp atomMem with
    ⟨carrier, _carrierMem, carrierEq⟩
  cases carrier <;>
    simp [periodicCarrierNodeToPlanarSATVariable] at carrierEq

theorem
    embeddedPeriodicCarrierClauses_dedup_crossoverInternal_count_eq_zero
    {Variable : Type*} [DecidableEq Variable]
    (clauses : List (PeriodicClause PeriodicCarrierNode))
    (internal : CrossingRecord × CrossoverInternal) :
    (PeriodicCNF.variableOccurrences
      ⟨(clauses.map
        (@embedPeriodicCarrierClause Variable)).dedup⟩).count
          (.crossoverInternal internal) = 0 := by
  rw [List.dedup_map_of_injective
    (@embedPeriodicCarrierClause_injective Variable)]
  change
    (embedPeriodicCarrierFormula
      (Variable := Variable)
      ⟨clauses.dedup⟩).variableOccurrences.count
        (.crossoverInternal internal) = 0
  apply List.count_eq_zero_of_not_mem
  rw [embedPeriodicCarrierFormula_variableOccurrences]
  intro internalMem
  rcases List.mem_map.mp internalMem with
    ⟨carrier, _carrierMem, carrierEq⟩
  cases carrier <;>
    simp [periodicCarrierNodeToPlanarSATVariable] at carrierEq

theorem
    deduplicatedNormalizedRoutedClauseFormula_atom_count_eq_zero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (atom : Variable) :
    (deduplicatedNormalizedRoutedClauseFormula
      formula).variableOccurrences.count (.atom atom) = 0 := by
  apply List.count_eq_zero_of_not_mem
  intro atomMem
  rcases List.mem_flatMap.mp atomMem with
    ⟨clause, clauseMem, atomMem⟩
  have clauseRaw :
      clause ∈ normalizedRoutedClauseClauses formula :=
    List.mem_dedup.mp clauseMem
  rcases normalizedRoutedClause_mem_witness
    formula clauseRaw with
      ⟨site, _siteMem, clauseEq⟩
  rw [clauseEq] at atomMem
  rcases List.mem_map.mp atomMem with
    ⟨literal, literalMem, atomEq⟩
  rcases List.mem_map.mp literalMem with
    ⟨taggedIncidence, _taggedMem, literalEq⟩
  have impossible :
      (routedSourcePeriodicLiteral
        formula (0, 0) taggedIncidence).atom = .atom atom :=
    (congrArg PeriodicLiteral.atom literalEq).trans atomEq
  simp [routedSourcePeriodicLiteral] at impossible

theorem
    deduplicatedNormalizedRoutedClauseFormula_boundary_count_eq_zero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (boundary : CrossingBoundary) :
    (deduplicatedNormalizedRoutedClauseFormula
      formula).variableOccurrences.count
        (.boundary boundary) = 0 := by
  apply List.count_eq_zero_of_not_mem
  intro boundaryMem
  rcases List.mem_flatMap.mp boundaryMem with
    ⟨clause, clauseMem, boundaryMem⟩
  have clauseRaw :
      clause ∈ normalizedRoutedClauseClauses formula :=
    List.mem_dedup.mp clauseMem
  rcases normalizedRoutedClause_mem_witness
    formula clauseRaw with
      ⟨site, _siteMem, clauseEq⟩
  rw [clauseEq] at boundaryMem
  rcases List.mem_map.mp boundaryMem with
    ⟨literal, literalMem, boundaryEq⟩
  rcases List.mem_map.mp literalMem with
    ⟨taggedIncidence, _taggedMem, literalEq⟩
  have impossible :
      (routedSourcePeriodicLiteral
        formula (0, 0) taggedIncidence).atom =
          .boundary boundary :=
    (congrArg PeriodicLiteral.atom literalEq).trans boundaryEq
  simp [routedSourcePeriodicLiteral] at impossible

theorem
    deduplicatedNormalizedRoutedClauseFormula_crossoverInternal_count_eq_zero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (internal : CrossingRecord × CrossoverInternal) :
    (deduplicatedNormalizedRoutedClauseFormula
      formula).variableOccurrences.count
        (.crossoverInternal internal) = 0 := by
  apply List.count_eq_zero_of_not_mem
  intro internalMem
  rcases List.mem_flatMap.mp internalMem with
    ⟨clause, clauseMem, internalMem⟩
  have clauseRaw :
      clause ∈ normalizedRoutedClauseClauses formula :=
    List.mem_dedup.mp clauseMem
  rcases normalizedRoutedClause_mem_witness
    formula clauseRaw with
      ⟨site, _siteMem, clauseEq⟩
  rw [clauseEq] at internalMem
  rcases List.mem_map.mp internalMem with
    ⟨literal, literalMem, internalEq⟩
  rcases List.mem_map.mp literalMem with
    ⟨taggedIncidence, _taggedMem, literalEq⟩
  have impossible :
      (routedSourcePeriodicLiteral
        formula (0, 0) taggedIncidence).atom =
          .crossoverInternal internal :=
    (congrArg PeriodicLiteral.atom literalEq).trans internalEq
  simp [routedSourcePeriodicLiteral] at impossible

theorem
    deduplicatedNormalizedRoutedVariableFormula_boundary_count_eq_zero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (boundary : CrossingBoundary) :
    (deduplicatedNormalizedRoutedVariableFormula
      formula).variableOccurrences.count
        (.boundary boundary) = 0 := by
  unfold deduplicatedNormalizedRoutedVariableFormula
  apply
    PeriodicEquality.normalizedFormulaClauses_dedup_count_eq_zero_of_endpoints
  intro link linkMem
  rcases drawingRoutedVariableLink_witness
    formula linkMem with
      ⟨site, occurrence, _occurrenceMem, _siteEq,
        firstEq, secondEq⟩
  rw [firstEq, secondEq]
  simp [normalizePlanarSATNode]

theorem
    deduplicatedNormalizedRoutedVariableFormula_crossoverInternal_count_eq_zero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (internal : CrossingRecord × CrossoverInternal) :
    (deduplicatedNormalizedRoutedVariableFormula
      formula).variableOccurrences.count
        (.crossoverInternal internal) = 0 := by
  unfold deduplicatedNormalizedRoutedVariableFormula
  apply
    PeriodicEquality.normalizedFormulaClauses_dedup_count_eq_zero_of_endpoints
  intro link linkMem
  rcases drawingRoutedVariableLink_witness
    formula linkMem with
      ⟨site, occurrence, _occurrenceMem, _siteEq,
        firstEq, secondEq⟩
  rw [firstEq, secondEq]
  simp [normalizePlanarSATNode]

theorem
    componentwiseDeduplicatedDrawingPeriodicPlanarSATFormula_atom_count_le_six
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (occurrences : formula.OccurrencesAtMost 3)
    (atom : Variable) :
    (componentwiseDeduplicatedDrawingPeriodicPlanarSATFormula
      formula).variableOccurrences.count (.atom atom) ≤ 6 := by
  have crossoverZero :
      (PeriodicCNF.variableOccurrences
        ⟨(normalizedScopedDrawingCrossoverClauses
          formula).dedup⟩).count (.atom atom) = 0 :=
    normalizedScopedDrawingCrossoverClauses_atom_count_eq_zero
      formula atom
  have carrierZero :
      (PeriodicCNF.variableOccurrences
        ⟨(embeddedNormalizedCompleteCarrierClauses
          formula).dedup⟩).count (.atom atom) = 0 := by
    unfold embeddedNormalizedCompleteCarrierClauses
    exact
      embeddedPeriodicCarrierClauses_dedup_atom_count_eq_zero
        _ atom
  have bendZero :
      (PeriodicCNF.variableOccurrences
        ⟨(embeddedNormalizedRouteBendClauses
          formula).dedup⟩).count (.atom atom) = 0 := by
    unfold embeddedNormalizedRouteBendClauses
    exact
      embeddedPeriodicCarrierClauses_dedup_atom_count_eq_zero
        _ atom
  have clauseZero :=
    deduplicatedNormalizedRoutedClauseFormula_atom_count_eq_zero
      formula atom
  have variableLe :=
    deduplicatedNormalizedRoutedVariableFormula_atom_count_le_six
      occurrences atom
  have clauseZero' :
      (PeriodicCNF.variableOccurrences
        ⟨(normalizedRoutedClauseClauses
          formula).dedup⟩).count (.atom atom) = 0 := by
    exact clauseZero
  have variableLe' :
      (PeriodicCNF.variableOccurrences
        ⟨(PeriodicEquality.normalizedFormulaClauses
          (normalizePlanarSATNode
            (PeriodicCNF.incidenceGraph formula))
          (drawingRoutedVariableLinks formula)).dedup⟩).count
            (.atom atom) ≤ 6 := by
    exact variableLe
  calc
    _ =
        (PeriodicCNF.variableOccurrences
          ⟨(normalizedScopedDrawingCrossoverClauses
            formula).dedup⟩).count (.atom atom) +
        ((PeriodicCNF.variableOccurrences
          ⟨(embeddedNormalizedCompleteCarrierClauses
            formula).dedup⟩).count (.atom atom) +
        ((PeriodicCNF.variableOccurrences
          ⟨(embeddedNormalizedRouteBendClauses
            formula).dedup⟩).count (.atom atom) +
        ((PeriodicCNF.variableOccurrences
          ⟨(normalizedRoutedClauseClauses
            formula).dedup⟩).count (.atom atom) +
        (PeriodicCNF.variableOccurrences
          ⟨(PeriodicEquality.normalizedFormulaClauses
            (normalizePlanarSATNode
              (PeriodicCNF.incidenceGraph formula))
            (drawingRoutedVariableLinks formula)).dedup⟩).count
              (.atom atom)))) :=
      componentwiseDeduplicatedDrawingPeriodicPlanarSATFormula_atom_occurrence_count
        formula atom
    _ ≤ 6 := by
      rw [crossoverZero, carrierZero, bendZero, clauseZero']
      omega

theorem
    componentwiseDeduplicatedDrawingPeriodicPlanarSATFormula_boundary_count_le_six
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (boundary : CrossingBoundary) :
    (componentwiseDeduplicatedDrawingPeriodicPlanarSATFormula
      formula).variableOccurrences.count
        (.boundary boundary) ≤ 6 := by
  have crossoverLe :=
    normalizedScopedDrawingCrossoverClauses_boundary_count_le_two
      wellFormed degree isLocal boundary
  have carrierLe :=
    embeddedNormalizedCompleteCarrierClauses_boundary_count_le_four
      formula boundary
  have bendZero :=
    embeddedNormalizedRouteBendClauses_boundary_count_eq_zero
      formula boundary
  have clauseZero :=
    deduplicatedNormalizedRoutedClauseFormula_boundary_count_eq_zero
      formula boundary
  have variableZero :=
    deduplicatedNormalizedRoutedVariableFormula_boundary_count_eq_zero
      formula boundary
  have clauseZero' :
      (PeriodicCNF.variableOccurrences
        ⟨(normalizedRoutedClauseClauses
          formula).dedup⟩).count
            (.boundary boundary) = 0 :=
    clauseZero
  have variableZero' :
      (PeriodicCNF.variableOccurrences
        ⟨(PeriodicEquality.normalizedFormulaClauses
          (normalizePlanarSATNode
            (PeriodicCNF.incidenceGraph formula))
          (drawingRoutedVariableLinks formula)).dedup⟩).count
            (.boundary boundary) = 0 :=
    variableZero
  calc
    _ =
        (PeriodicCNF.variableOccurrences
          ⟨(normalizedScopedDrawingCrossoverClauses
            formula).dedup⟩).count (.boundary boundary) +
        ((PeriodicCNF.variableOccurrences
          ⟨(embeddedNormalizedCompleteCarrierClauses
            formula).dedup⟩).count (.boundary boundary) +
        ((PeriodicCNF.variableOccurrences
          ⟨(embeddedNormalizedRouteBendClauses
            formula).dedup⟩).count (.boundary boundary) +
        ((PeriodicCNF.variableOccurrences
          ⟨(normalizedRoutedClauseClauses
            formula).dedup⟩).count (.boundary boundary) +
        (PeriodicCNF.variableOccurrences
          ⟨(PeriodicEquality.normalizedFormulaClauses
            (normalizePlanarSATNode
              (PeriodicCNF.incidenceGraph formula))
            (drawingRoutedVariableLinks formula)).dedup⟩).count
              (.boundary boundary)))) :=
      componentwiseDeduplicatedDrawingPeriodicPlanarSATFormula_occurrence_count
        formula (.boundary boundary)
    _ ≤ 6 := by
      rw [bendZero, clauseZero', variableZero']
      omega

theorem
    componentwiseDeduplicatedDrawingPeriodicPlanarSATFormula_crossoverInternal_count_le_eight
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (internal : CrossingRecord × CrossoverInternal) :
    (componentwiseDeduplicatedDrawingPeriodicPlanarSATFormula
      formula).variableOccurrences.count
        (.crossoverInternal internal) ≤ 8 := by
  have crossoverLe :=
    normalizedScopedDrawingCrossoverClauses_internal_count_le_eight
      wellFormed degree isLocal internal
  have carrierZero :
      (PeriodicCNF.variableOccurrences
        ⟨(embeddedNormalizedCompleteCarrierClauses
          formula).dedup⟩).count
            (.crossoverInternal internal) = 0 := by
    unfold embeddedNormalizedCompleteCarrierClauses
    exact
      embeddedPeriodicCarrierClauses_dedup_crossoverInternal_count_eq_zero
        _ internal
  have bendZero :
      (PeriodicCNF.variableOccurrences
        ⟨(embeddedNormalizedRouteBendClauses
          formula).dedup⟩).count
            (.crossoverInternal internal) = 0 := by
    unfold embeddedNormalizedRouteBendClauses
    exact
      embeddedPeriodicCarrierClauses_dedup_crossoverInternal_count_eq_zero
        _ internal
  have clauseZero :=
    deduplicatedNormalizedRoutedClauseFormula_crossoverInternal_count_eq_zero
      formula internal
  have variableZero :=
    deduplicatedNormalizedRoutedVariableFormula_crossoverInternal_count_eq_zero
      formula internal
  have clauseZero' :
      (PeriodicCNF.variableOccurrences
        ⟨(normalizedRoutedClauseClauses
          formula).dedup⟩).count
            (.crossoverInternal internal) = 0 :=
    clauseZero
  have variableZero' :
      (PeriodicCNF.variableOccurrences
        ⟨(PeriodicEquality.normalizedFormulaClauses
          (normalizePlanarSATNode
            (PeriodicCNF.incidenceGraph formula))
          (drawingRoutedVariableLinks formula)).dedup⟩).count
            (.crossoverInternal internal) = 0 :=
    variableZero
  calc
    _ =
        (PeriodicCNF.variableOccurrences
          ⟨(normalizedScopedDrawingCrossoverClauses
            formula).dedup⟩).count
              (.crossoverInternal internal) +
        ((PeriodicCNF.variableOccurrences
          ⟨(embeddedNormalizedCompleteCarrierClauses
            formula).dedup⟩).count
              (.crossoverInternal internal) +
        ((PeriodicCNF.variableOccurrences
          ⟨(embeddedNormalizedRouteBendClauses
            formula).dedup⟩).count
              (.crossoverInternal internal) +
        ((PeriodicCNF.variableOccurrences
          ⟨(normalizedRoutedClauseClauses
            formula).dedup⟩).count
              (.crossoverInternal internal) +
        (PeriodicCNF.variableOccurrences
          ⟨(PeriodicEquality.normalizedFormulaClauses
            (normalizePlanarSATNode
              (PeriodicCNF.incidenceGraph formula))
            (drawingRoutedVariableLinks formula)).dedup⟩).count
              (.crossoverInternal internal)))) :=
      componentwiseDeduplicatedDrawingPeriodicPlanarSATFormula_occurrence_count
        formula (.crossoverInternal internal)
    _ ≤ 8 := by
      rw [carrierZero, bendZero, clauseZero', variableZero']
      omega

end PeriodicOrthocrossing
end LeanTrominoes
