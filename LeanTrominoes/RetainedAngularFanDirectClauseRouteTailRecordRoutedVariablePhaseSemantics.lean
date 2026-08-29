/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanDirectClauseRouteTailRecordPhaseFilter
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryTemplates

/-! # Fixed routed-variable route-tail phase table -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

/-- Each routed-variable template records a duplicator atlas key. -/
@[simp] theorem retainedFinalDirectRoutedVariableClauseQuery_isDirectRouted
    (arm : PlanarThreeSAT.DuplicatorArm)
    (nextSlice forward : Bool) :
    (retainedFinalDirectRoutedVariableClauseQuery
      arm nextSlice forward).isDirectRouted = true := by
  cases arm <;> cases nextSlice <;> cases forward <;> rfl

/-- A duplicator atlas key is never a crossover key. -/
@[simp] theorem retainedFinalDirectRoutedVariableClauseQuery_notDirectCrossover
    (arm : PlanarThreeSAT.DuplicatorArm)
    (nextSlice forward : Bool) :
    (retainedFinalDirectRoutedVariableClauseQuery
      arm nextSlice forward).isDirectCrossover = false := by
  cases arm <;> cases nextSlice <;> cases forward <;> rfl

/-- Every query in the fixed six-clause duplicator block belongs to the
routed phase and not to the crossover phase. -/
theorem retainedFinalDirectRoutedVariableFullSiteQueries_phase :
    (∀ query ∈ retainedFinalDirectRoutedVariableFullSiteQueries,
      query.isDirectRouted = true) ∧
    (∀ query ∈ retainedFinalDirectRoutedVariableFullSiteQueries,
      query.isDirectCrossover = false) := by
  simp [retainedFinalDirectRoutedVariableFullSiteQueries,
    retainedFinalDirectRoutedVariableCurrentArmQueries]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
