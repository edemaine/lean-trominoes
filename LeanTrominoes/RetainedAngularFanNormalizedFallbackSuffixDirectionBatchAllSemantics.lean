/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanNormalizedFallbackSuffixDirectionBatchSemantics
import LeanTrominoes.RetainedAngularFanNormalizedFallbackSuffixEscapedSemantics

/-! # Mixed-policy semantics of batched normalized fallback queries -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit
namespace NormalizedFallbackSuffixDirectionCompiler
namespace Batch

open FallbackSuffixDirectionCompiler

/-- Canonical normalized suffixes represented by an arbitrary query batch. -/
def retainedDirections
    (queries : List Query) : List OutputToken :=
  queries.flatMap fun query =>
    directionTokens
        (retainedNormalizedFallbackFanSuffixDirections
          query.kind
          (scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor
            (query.direction, query.rawLength)) query.slot) ++
      [.routeEnd]

/-- Every positive mixed-policy batch compiles to its canonical normalized
suffix words. -/
theorem directions_eq_retainedDirections
    (queries : List Query)
    (lengthPositive : ∀ query ∈ queries, 0 < query.rawLength) :
    directions queries = retainedDirections queries := by
  induction queries with
  | nil => rfl
  | cons query queries induction =>
      have queryPositive : 0 < query.rawLength :=
        lengthPositive query (by simp)
      have restPositive :
          ∀ rest ∈ queries, 0 < rest.rawLength := by
        intro rest restMember
        exact lengthPositive rest (by simp [restMember])
      change
        (directionTokens
            (compiledDirections query.kind query.direction
              query.rawLength query.slot) ++ [.routeEnd]) ++
            directions queries =
          (directionTokens
              (retainedNormalizedFallbackFanSuffixDirections
                query.kind
                (scaleRetainedTerminalData
                  retainedAngularFanSourceClearanceFactor
                  (query.direction, query.rawLength)) query.slot) ++
            [.routeEnd]) ++ retainedDirections queries
      cases query.kind with
      | ordinary =>
          rw [compiledDirections_eq_ordinary_normalizedSuffix
            query.direction query.rawLength query.slot queryPositive,
            induction restPositive]
      | escaped =>
          rw [compiledDirections_eq_escaped_normalizedSuffix
            query.direction query.rawLength query.slot queryPositive,
            induction restPositive]

end Batch
end NormalizedFallbackSuffixDirectionCompiler
end PeriodicEightOccurrenceSplit
end LeanTrominoes
