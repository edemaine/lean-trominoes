/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackSuffixDirectionBatchCompiler
import LeanTrominoes.RetainedAngularFanFallbackSuffixDirectionSemantics

/-! # Geometric semantics of batched fallback-suffix queries -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit
namespace FallbackSuffixDirectionCompiler
namespace Batch

/-- Actual route-delimited fallback suffixes represented by a query batch. -/
def retainedDirections (queries : List Query) : List OutputToken :=
  queries.flatMap fun query =>
    directionTokens
        (retainedFallbackFanSuffixDirections query.kind
          (scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor
            (query.direction, query.rawLength)) query.slot) ++
      [.routeEnd]

/-- When every raw route terminal is positive, the compiled batch is exactly
the corresponding batch of geometric fallback suffixes. -/
theorem directions_eq_retainedDirections
    (queries : List Query)
    (lengthPositive : ∀ query ∈ queries, 0 < query.rawLength) :
    directions queries = retainedDirections queries := by
  induction queries with
  | nil => rfl
  | cons query queries induction =>
      have queryPositive : 0 < query.rawLength :=
        lengthPositive query (by simp)
      have restPositive : ∀ rest ∈ queries, 0 < rest.rawLength := by
        intro rest restMember
        exact lengthPositive rest (by simp [restMember])
      change
        (directionTokens
            (compiledDirections query.kind query.direction
              query.rawLength query.slot) ++ [.routeEnd]) ++
            directions queries =
          (directionTokens
              (retainedFallbackFanSuffixDirections query.kind
                (scaleRetainedTerminalData
                  retainedAngularFanSourceClearanceFactor
                  (query.direction, query.rawLength)) query.slot) ++
            [.routeEnd]) ++ retainedDirections queries
      rw [compiledDirections_eq_retainedFallbackFanSuffixDirections
        query.kind query.direction query.rawLength query.slot queryPositive,
        induction restPositive]

end Batch
end FallbackSuffixDirectionCompiler
end PeriodicEightOccurrenceSplit
end LeanTrominoes
