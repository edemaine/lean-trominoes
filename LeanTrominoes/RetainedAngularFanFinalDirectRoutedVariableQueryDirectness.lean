/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalDirectClauseQueryTemplateDirectness

/-! # Directness of the fixed final routed-variable query site -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- Every individual stable routed-variable template is all-direct. -/
theorem retainedFinalDirectRoutedVariableClauseQuery_allDirect
    (arm : PlanarThreeSAT.DuplicatorArm)
    (nextSlice forward : Bool) :
    (retainedFinalDirectRoutedVariableClauseQuery
      arm nextSlice forward).AllDirect := by
  cases forward <;>
    unfold retainedFinalDirectRoutedVariableClauseQuery
      routedVariableClauseDescriptor
      RetainedFinalCopiedClauseQuery.directOfToken <;>
    exact RetainedFinalCopiedClauseQuery.allDirect_directOfProfile _ _

/-- The fixed six-query routed-variable site contains only direct fields. -/
theorem retainedFinalDirectRoutedVariableFullSiteQueries_allDirect :
    ∀ query ∈ retainedFinalDirectRoutedVariableFullSiteQueries,
      query.AllDirect := by
  intro query queryMember
  simp only [retainedFinalDirectRoutedVariableFullSiteQueries,
    retainedFinalDirectRoutedVariableCurrentArmQueries,
    List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at queryMember
  rcases queryMember with
    ((rfl | rfl) | (rfl | rfl)) | (rfl | rfl)
  all_goals
    apply retainedFinalDirectRoutedVariableClauseQuery_allDirect

end PeriodicEightOccurrenceSplit
end LeanTrominoes
