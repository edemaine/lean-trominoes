/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQuery

/-! # List semantics of final copied-clause queries -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

/-- Evaluating clause queries commutes with concatenation. -/
@[simp] theorem retainedFinalCopiedClauseDescriptors_append
    (first second : List RetainedFinalCopiedClauseQuery) :
    retainedFinalCopiedClauseDescriptors (first ++ second) =
      retainedFinalCopiedClauseDescriptors first ++
        retainedFinalCopiedClauseDescriptors second := by
  simp [retainedFinalCopiedClauseDescriptors]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
