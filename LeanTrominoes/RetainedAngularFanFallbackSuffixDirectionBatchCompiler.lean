/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackSuffixDirectionCompiler
import LeanTrominoes.TM2PolyTimeInputEncodingTransport

/-! # Batched compact fallback-suffix direction queries -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit
namespace FallbackSuffixDirectionCompiler
namespace Batch

open Computability Turing FiniteStateTransducer

/-- Semantic data represented by one compact fallback-suffix query. -/
structure Query where
  kind : RetainedFallbackFanKind
  direction : RetainedTerminalDirection
  rawLength : Nat
  slot : RetainedTerminalSlot

/-- Concatenate the compact kind/direction/slot/unary-length encodings. -/
def encode (queries : List Query) : List Token :=
  queries.flatMap fun query =>
    queryTokens query.kind query.direction query.rawLength query.slot

/-- Exact route-delimited direction stream represented by a query list. -/
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
      change scan transition initial
          (queryTokens query.kind query.direction query.rawLength query.slot ++
            encode queries) =
        (initial,
          (directionTokens
              (compiledDirections query.kind query.direction
                query.rawLength query.slot) ++
            [.routeEnd]) ++ directions queries)
      rw [scan_append, scan_queryTokens]
      dsimp only
      rw [induction]

/-- The existing suffix transducer maps a whole compact query batch to its
exact concatenated route words. -/
@[simp] theorem output_encode (queries : List Query) :
    output (encode queries) = directions queries := by
  unfold output FiniteStateTransducer.output
  rw [scan_encode]
  simp [finish]

/-- Batched fallback-suffix compilation is polynomial time under the compact
query encoding. -/
noncomputable def directionsComputableInPolyTime :
    TM2ComputableInPolyTime encode id directions :=
  TM2PolyTimeInputEncodingTransport.of_prepare encode
    outputComputableInPolyTime
    (fun _ => rfl)
    output_encode

end Batch
end FallbackSuffixDirectionCompiler
end PeriodicEightOccurrenceSplit
end LeanTrominoes

end
