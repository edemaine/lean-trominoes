/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceMetadataSize
import LeanTrominoes.PeriodicThreeSATThreeCycleIncidenceData
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceIncidenceSemantics

/-! # Exact cycle-incidence suffix of occurrence splitting -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- The complete split-formula incidence stream is the copied source stream
followed by the shifted implication-cycle stream. -/
theorem formula_incidencesWithMetadata_eq_occurrence_append_cycle
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PeriodicCNF.incidencesWithMetadata (formula source) =
      occurrenceIncidences source ++ cycleIncidences source := by
  change
    PeriodicCNF.incidencesWithMetadata
      (PeriodicCNF.mk
        (occurrenceClauses source ++ allCycleClauses source)) = _
  rw [PeriodicCNF.incidencesWithMetadata_append,
    incidencesWithMetadata_occurrenceClauses]
  simp [cycleIncidences]

/-- The cycle suffix contributes exactly two routes per source literal. -/
@[simp] theorem cycleIncidences_length
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (cycleIncidences source).length =
      2 * PeriodicCNF.presentationLiteralCount source := by
  have lengths := congrArg List.length
    (formula_incidencesWithMetadata_eq_occurrence_append_cycle source)
  simp only [List.length_append] at lengths
  rw [PeriodicCNF.incidencesWithMetadata_length,
    formula_presentationLiteralCount,
    occurrenceIncidences_length] at lengths
  omega

end PeriodicThreeSATThree
end LeanTrominoes
