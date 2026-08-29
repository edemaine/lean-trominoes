/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryDirectness
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryTemplates

/-! # Directness of stable final clause-query templates -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- Replacing a directed profile by finite-atlas queries makes every one of
its incidence fields direct. -/
theorem RetainedFinalCopiedClauseQuery.allDirect_directOfProfile
    (kind : RetainedDirectClauseKind)
    (profile : FormulaShapeDirectionOrdering.DirectedClauseProfile) :
    (RetainedFinalCopiedClauseQuery.directOfProfile
      kind profile).AllDirect := by
  cases profile <;>
    simp [RetainedFinalCopiedClauseQuery.directOfProfile,
      RetainedFinalCopiedClauseQuery.AllDirect,
      RetainedFinalCopiedSourceDirectionQuery.IsDirect]

/-- Every stable routed-clause template is all-direct. -/
theorem retainedFinalDirectRoutedClauseQuery_allDirect
    (profiles : List UnaryProgramClauseProfile.LiteralProfile) :
    (retainedFinalDirectRoutedClauseQuery profiles).AllDirect := by
  unfold retainedFinalDirectRoutedClauseQuery routedClauseDescriptor
    RetainedFinalCopiedClauseQuery.directOfToken
  exact RetainedFinalCopiedClauseQuery.allDirect_directOfProfile _ _

end PeriodicEightOccurrenceSplit
end LeanTrominoes
