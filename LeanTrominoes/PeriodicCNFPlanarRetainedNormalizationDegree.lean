import LeanTrominoes.PeriodicCNFPlanarRetainedNormalizationComponents
import LeanTrominoes.PeriodicCNFPlanarTerminalNormalizationDegree

/-!
# Degree eight for normalized retained planar SAT

The retained straight-carrier family has normalized degree four.  Combining
that sharper estimate with the unchanged crossover, bend, routed-clause, and
routed-variable bounds gives degree eight for the complete unwrapped
retained formula after global clause deduplication.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

/-- Embedding the retained normalized carrier family preserves its
degree-four bound at every carrier prototype. -/
theorem
    embeddedNormalizedRetainedCompleteCarrierClauses_count_le_four
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (target : PeriodicCarrierNode) :
    (PeriodicCNF.variableOccurrences
      ⟨(embeddedNormalizedRetainedCompleteCarrierClauses
        formula).dedup⟩).count
          (periodicCarrierNodeToPlanarSATVariable target) ≤ 4 := by
  cases target with
  | terminal indexed endpoint =>
      unfold embeddedNormalizedRetainedCompleteCarrierClauses
      simp only [periodicCarrierNodeToPlanarSATVariable]
      rw [embeddedPeriodicCarrierClauses_dedup_terminal_count]
      exact
        deduplicatedNormalizedRetainedCompleteCarrierFormula_occurrencesAtMostFour
          wellFormed degree isLocal (.terminal indexed endpoint)
  | boundary boundary =>
      unfold embeddedNormalizedRetainedCompleteCarrierClauses
      simp only [periodicCarrierNodeToPlanarSATVariable]
      rw [embeddedPeriodicCarrierClauses_dedup_boundary_count]
      exact
        deduplicatedNormalizedRetainedCompleteCarrierFormula_occurrencesAtMostFour
          wellFormed degree isLocal (.boundary boundary)

/-- Separately deduplicating the five retained normalized components yields
degree at most eight. -/
theorem
    componentwiseDeduplicatedRetainedDrawingPeriodicPlanarSATFormula_occurrencesAtMostEight
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (occurrences : formula.OccurrencesAtMost 3) :
    (componentwiseDeduplicatedRetainedDrawingPeriodicPlanarSATFormula
      formula).OccurrencesAtMost 8 := by
  intro output
  rw [
    componentwiseDeduplicatedRetainedDrawingPeriodicPlanarSATFormula_occurrence_count]
  cases output with
  | terminal indexed endpoint =>
      have crossoverZero :
          (PeriodicCNF.variableOccurrences
            ⟨(normalizedScopedDrawingCrossoverClauses
              formula).dedup⟩).count
                (.terminal indexed endpoint) = 0 :=
        normalizedScopedDrawingCrossoverClauses_terminal_count_eq_zero
          formula indexed endpoint
      have carrierLe :
          (PeriodicCNF.variableOccurrences
            ⟨(embeddedNormalizedRetainedCompleteCarrierClauses
              formula).dedup⟩).count
                (.terminal indexed endpoint) ≤ 4 := by
        exact
          embeddedNormalizedRetainedCompleteCarrierClauses_count_le_four
            wellFormed degree isLocal (.terminal indexed endpoint)
      have bendLe :
          (PeriodicCNF.variableOccurrences
            ⟨(embeddedNormalizedRouteBendClauses
              formula).dedup⟩).count
                (.terminal indexed endpoint) ≤ 2 :=
        embeddedNormalizedRouteBendClauses_terminal_count_le_two
          formula indexed endpoint
      cases endpoint with
      | start =>
          have clauseLe :
              (PeriodicCNF.variableOccurrences
                ⟨(normalizedRoutedClauseClauses
                  formula).dedup⟩).count
                    (.terminal indexed .start) ≤ 1 :=
            deduplicatedNormalizedRoutedClauseFormula_terminal_count_le_one
              formula indexed
          have variableZero :
              (PeriodicCNF.variableOccurrences
                ⟨(PeriodicEquality.normalizedFormulaClauses
                  (normalizePlanarSATNode
                    (PeriodicCNF.incidenceGraph formula))
                  (drawingRoutedVariableLinks
                    formula)).dedup⟩).count
                      (.terminal indexed .start) = 0 :=
            deduplicatedNormalizedRoutedVariableFormula_start_count_eq_zero
              formula indexed
          rw [crossoverZero, variableZero]
          omega
      | finish =>
          have clauseZero :
              (PeriodicCNF.variableOccurrences
                ⟨(normalizedRoutedClauseClauses
                  formula).dedup⟩).count
                    (.terminal indexed .finish) = 0 :=
            deduplicatedNormalizedRoutedClauseFormula_finish_count_eq_zero
              formula indexed
          have variableLe :
              (PeriodicCNF.variableOccurrences
                ⟨(PeriodicEquality.normalizedFormulaClauses
                  (normalizePlanarSATNode
                    (PeriodicCNF.incidenceGraph formula))
                  (drawingRoutedVariableLinks
                    formula)).dedup⟩).count
                      (.terminal indexed .finish) ≤ 2 :=
            deduplicatedNormalizedRoutedVariableFormula_terminal_count_le_two
              formula indexed
          rw [crossoverZero, clauseZero]
          omega
  | boundary boundary =>
      have crossoverLe :=
        normalizedScopedDrawingCrossoverClauses_boundary_count_le_two
          wellFormed degree isLocal boundary
      have carrierLe :
          (PeriodicCNF.variableOccurrences
            ⟨(embeddedNormalizedRetainedCompleteCarrierClauses
              formula).dedup⟩).count
                (.boundary boundary) ≤ 4 := by
        exact
          embeddedNormalizedRetainedCompleteCarrierClauses_count_le_four
            wellFormed degree isLocal (.boundary boundary)
      have bendZero :=
        embeddedNormalizedRouteBendClauses_boundary_count_eq_zero
          formula boundary
      have clauseZero :
          (PeriodicCNF.variableOccurrences
            ⟨(normalizedRoutedClauseClauses
              formula).dedup⟩).count
                (.boundary boundary) = 0 :=
        deduplicatedNormalizedRoutedClauseFormula_boundary_count_eq_zero
          formula boundary
      have variableZero :
          (PeriodicCNF.variableOccurrences
            ⟨(PeriodicEquality.normalizedFormulaClauses
              (normalizePlanarSATNode
                (PeriodicCNF.incidenceGraph formula))
              (drawingRoutedVariableLinks formula)).dedup⟩).count
                  (.boundary boundary) = 0 :=
        deduplicatedNormalizedRoutedVariableFormula_boundary_count_eq_zero
          formula boundary
      rw [bendZero, clauseZero, variableZero]
      omega
  | atom atom =>
      have crossoverZero :=
        normalizedScopedDrawingCrossoverClauses_atom_count_eq_zero
          formula atom
      have carrierZero :
          (PeriodicCNF.variableOccurrences
            ⟨(embeddedNormalizedRetainedCompleteCarrierClauses
              formula).dedup⟩).count (.atom atom) = 0 := by
        unfold embeddedNormalizedRetainedCompleteCarrierClauses
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
      have clauseZero :
          (PeriodicCNF.variableOccurrences
            ⟨(normalizedRoutedClauseClauses
              formula).dedup⟩).count (.atom atom) = 0 :=
        deduplicatedNormalizedRoutedClauseFormula_atom_count_eq_zero
          formula atom
      have variableLe :
          (PeriodicCNF.variableOccurrences
            ⟨(PeriodicEquality.normalizedFormulaClauses
              (normalizePlanarSATNode
                (PeriodicCNF.incidenceGraph formula))
              (drawingRoutedVariableLinks formula)).dedup⟩).count
                  (.atom atom) ≤ 6 :=
        deduplicatedNormalizedRoutedVariableFormula_atom_count_le_six
          occurrences atom
      rw [crossoverZero, carrierZero, bendZero, clauseZero]
      omega
  | crossoverInternal internal =>
      have crossoverLe :=
        normalizedScopedDrawingCrossoverClauses_internal_count_le_eight
          wellFormed degree isLocal internal
      have carrierZero :
          (PeriodicCNF.variableOccurrences
            ⟨(embeddedNormalizedRetainedCompleteCarrierClauses
              formula).dedup⟩).count
                (.crossoverInternal internal) = 0 := by
        unfold embeddedNormalizedRetainedCompleteCarrierClauses
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
      have clauseZero :
          (PeriodicCNF.variableOccurrences
            ⟨(normalizedRoutedClauseClauses
              formula).dedup⟩).count
                (.crossoverInternal internal) = 0 :=
        deduplicatedNormalizedRoutedClauseFormula_crossoverInternal_count_eq_zero
          formula internal
      have variableZero :
          (PeriodicCNF.variableOccurrences
            ⟨(PeriodicEquality.normalizedFormulaClauses
              (normalizePlanarSATNode
                (PeriodicCNF.incidenceGraph formula))
              (drawingRoutedVariableLinks formula)).dedup⟩).count
                  (.crossoverInternal internal) = 0 :=
        deduplicatedNormalizedRoutedVariableFormula_crossoverInternal_count_eq_zero
          formula internal
      rw [carrierZero, bendZero, clauseZero, variableZero]
      omega

/-- The globally deduplicated unwrapped retained planar-SAT formula has at
most eight occurrences of every variable. -/
theorem
    retainedDeduplicatedDrawingPeriodicPlanarSATFormula_occurrencesAtMostEight
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (occurrences : formula.OccurrencesAtMost 3) :
    (retainedDeduplicatedDrawingPeriodicPlanarSATFormula
      formula).OccurrencesAtMost 8 := by
  intro output
  have sublist :=
    retainedDeduplicatedDrawingPeriodicPlanarSATFormula_variableOccurrences_sublist
      formula
  have outputLe :
      (retainedDeduplicatedDrawingPeriodicPlanarSATFormula
        formula).variableOccurrences.count output ≤
      (componentwiseDeduplicatedRetainedDrawingPeriodicPlanarSATFormula
        formula).variableOccurrences.count output :=
    sublist.subperm.count_le output
  exact outputLe.trans
    (componentwiseDeduplicatedRetainedDrawingPeriodicPlanarSATFormula_occurrencesAtMostEight
      wellFormed degree isLocal occurrences output)

end PeriodicOrthocrossing
end LeanTrominoes
