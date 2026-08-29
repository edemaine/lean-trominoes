/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseOccurrenceRoleSemantics

/-! # Listwise arity semantics of evaluated copied-clause descriptors -/

namespace LeanTrominoes.PeriodicEightOccurrenceSplit

/-- Evaluating a query list preserves every entry's represented occurrence
arity, not just their total sum. -/
theorem retainedFinalCopiedClauseDescriptorArities_eq_queryArities
    (queries : List RetainedFinalCopiedClauseQuery) :
    (retainedFinalCopiedClauseDescriptors queries).map
        retainedFinalCopiedDescriptorArity =
      queries.map retainedFinalCopiedClauseQueryArity := by
  induction queries with
  | nil => rfl
  | cons query queries induction =>
      change
        retainedFinalCopiedDescriptorArity
              (retainedFinalCopiedClauseDescriptorOfQuery query) ::
            (retainedFinalCopiedClauseDescriptors queries).map
              retainedFinalCopiedDescriptorArity =
          retainedFinalCopiedClauseQueryArity query ::
            queries.map retainedFinalCopiedClauseQueryArity
      rw [retainedFinalCopiedClauseQueryArity_eq_descriptor,
        induction]

end LeanTrominoes.PeriodicEightOccurrenceSplit
