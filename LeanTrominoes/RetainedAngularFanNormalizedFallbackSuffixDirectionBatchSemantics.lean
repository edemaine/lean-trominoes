/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanNormalizedFallbackSuffixDirectionBatchCompiler
import LeanTrominoes.RetainedAngularFanNormalizedFallbackSuffixOrdinarySemantics

/-! # Ordinary semantics of batched normalized fallback queries -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit
namespace NormalizedFallbackSuffixDirectionCompiler
namespace Batch

open FallbackSuffixDirectionCompiler

/-- Canonical normalized ordinary suffixes represented by a query batch. -/
def retainedOrdinaryDirections
    (queries : List Query) : List OutputToken :=
  queries.flatMap fun query =>
    directionTokens
        (retainedNormalizedFallbackFanSuffixDirections
          .ordinary
          (scaleRetainedTerminalData retainedAngularFanSourceClearanceFactor
            (query.direction, query.rawLength)) query.slot) ++
      [.routeEnd]

/-- A positive all-ordinary batch compiles exactly to its canonical
normalized suffix words. -/
theorem directions_eq_retainedOrdinaryDirections
    (queries : List Query)
    (ordinary : ∀ query ∈ queries, query.kind = .ordinary)
    (lengthPositive : ∀ query ∈ queries, 0 < query.rawLength) :
    directions queries = retainedOrdinaryDirections queries := by
  induction queries with
  | nil => rfl
  | cons query queries induction =>
      have queryOrdinary : query.kind = .ordinary :=
        ordinary query (by simp)
      have queryPositive : 0 < query.rawLength :=
        lengthPositive query (by simp)
      have restOrdinary :
          ∀ rest ∈ queries, rest.kind = .ordinary := by
        intro rest restMember
        exact ordinary rest (by simp [restMember])
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
                .ordinary
                (scaleRetainedTerminalData
                  retainedAngularFanSourceClearanceFactor
                  (query.direction, query.rawLength)) query.slot) ++
            [.routeEnd]) ++ retainedOrdinaryDirections queries
      rw [queryOrdinary,
        compiledDirections_eq_ordinary_normalizedSuffix
          query.direction query.rawLength query.slot queryPositive,
        induction restOrdinary restPositive]

end Batch
end NormalizedFallbackSuffixDirectionCompiler
end PeriodicEightOccurrenceSplit
end LeanTrominoes
