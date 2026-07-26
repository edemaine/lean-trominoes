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
        (planarSATCoreVariableMap coreLiteral.1)).1 =
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
        (planarSATCoreVariableMap coreLiteral.1)).1 =
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
          (PeriodicEquality.normalizeLink normalizeCarrierNode) :=
    List.mem_dedup.mp linkMem
  rcases List.mem_map.mp linkRaw with
    ⟨source, sourceMem, sourceEq⟩
  subst link
  have incident :
      (PeriodicEquality.normalizeLink
          normalizeCarrierNode source).first =
            .terminal indexed endpoint ∨
        (PeriodicEquality.normalizeLink
          normalizeCarrierNode source).second =
            .terminal indexed endpoint := by
    simpa [PeriodicEquality.normalizedLinkEndpoints,
      eq_comm] using endpointMem
  rcases (normalizedLink_incident_terminal_iff
    source indexed endpoint).mp incident with
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
          normalizePlanarSATNode
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
            normalizePlanarSATNode
            (drawingRoutedVariableLinks formula)).dedup⟩).count
              (.atom atom)))) :=
      componentwiseDeduplicatedDrawingPeriodicPlanarSATFormula_atom_occurrence_count
        formula atom
    _ ≤ 6 := by
      rw [crossoverZero, carrierZero, bendZero, clauseZero']
      omega

end PeriodicOrthocrossing
end LeanTrominoes
