/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackSuffixDirectionBatchCompiler
import LeanTrominoes.RetainedAngularFanNormalizedFallbackSuffixDirectionCompiler

/-! # Batched normalized fallback-suffix direction queries -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit
namespace NormalizedFallbackSuffixDirectionCompiler
namespace Batch

open Computability Turing FiniteStateTransducer
open FallbackSuffixDirectionCompiler

abbrev Query := FallbackSuffixDirectionCompiler.Batch.Query

/-- Normalized queries use the existing compact query representation. -/
def encode (queries : List Query) : List Token :=
  FallbackSuffixDirectionCompiler.Batch.encode queries

/-- Exact route-delimited normalized direction stream represented by a
query list. -/
def directions (queries : List Query) : List OutputToken :=
  queries.flatMap fun query =>
    directionTokens
        (compiledDirections query.kind query.direction
          query.rawLength query.slot) ++
      [.routeEnd]

theorem scan_encode (queries : List Query) :
    scan transition initial (encode queries) =
      (initial, directions queries) := by
  induction queries with
  | nil => rfl
  | cons query queries induction =>
      unfold encode at induction ⊢
      change scan transition initial
          (queryTokens query.kind query.direction query.rawLength query.slot ++
            FallbackSuffixDirectionCompiler.Batch.encode queries) =
        (initial,
          (directionTokens
              (compiledDirections query.kind query.direction
                query.rawLength query.slot) ++
            [.routeEnd]) ++ directions queries)
      rw [scan_append, scan_queryTokens]
      dsimp only
      rw [induction]

/-- The normalized suffix transducer maps a compact query batch to the
concatenated normalized route words. -/
@[simp] theorem output_encode (queries : List Query) :
    output (encode queries) = directions queries := by
  unfold output FiniteStateTransducer.output
  rw [scan_encode]
  simp [finish]

/-- Batched normalized suffix compilation is polynomial time under the
shared compact query encoding. -/
noncomputable def directionsComputableInPolyTime :
    TM2ComputableInPolyTime encode id directions :=
  TM2PolyTimeInputEncodingTransport.of_prepare encode
    outputComputableInPolyTime
    (fun _ => rfl)
    output_encode

end Batch
end NormalizedFallbackSuffixDirectionCompiler
end PeriodicEightOccurrenceSplit
end LeanTrominoes

end
