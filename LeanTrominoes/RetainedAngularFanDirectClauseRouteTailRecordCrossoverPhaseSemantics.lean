/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanDirectClauseRouteTailRecordPhaseFilter
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryTemplates

/-! # Fixed crossover route-tail phase table -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

/-- Every one of the 26 fixed crossover templates records its crossover key
and no routed key. -/
@[simp] theorem retainedFinalDirectCrossoverClauseQueryAt_phase
    (clauseIndex : Fin 26) :
    (retainedFinalDirectCrossoverClauseQueryAt
      clauseIndex).isDirectCrossover = true ∧
    (retainedFinalDirectCrossoverClauseQueryAt
      clauseIndex).isDirectRouted = false := by
  fin_cases clauseIndex <;> constructor <;> rfl

/-- List form of the fixed crossover table classification. -/
theorem retainedFinalDirectCrossoverClauseQueries_phase :
    (∀ query ∈ retainedFinalDirectCrossoverClauseQueries,
      query.isDirectCrossover = true) ∧
    (∀ query ∈ retainedFinalDirectCrossoverClauseQueries,
      query.isDirectRouted = false) := by
  simp [retainedFinalDirectCrossoverClauseQueries]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
