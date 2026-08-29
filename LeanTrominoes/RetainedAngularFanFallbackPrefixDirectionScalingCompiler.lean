/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.GadgetSparseRouteDirectionScalingCompiler
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequestBatchInnerCompiler

/-! # Fixed scaling of delimited retained fallback source-prefix words -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit
namespace FallbackPrefixDirectionScaling

open Computability Turing Gadget
open PeriodicThreeDM.NormalizationDirectionRequest.Batch

abbrev Token :=
  PeriodicThreeDM.NormalizationDirectionRequest.Batch.NormalizedToken

/-- Repeat source directions by the final fixed clearance factor while
preserving every route delimiter. -/
def block : Token → List Token
  | .direction direction => List.replicate 1152 (.direction direction)
  | .routeEnd => [.routeEnd]

def output (tokens : List Token) : List Token :=
  tokens.flatMap block

@[simp] theorem output_append (first second : List Token) :
    output (first ++ second) = output first ++ output second := by
  simp [output]

private theorem output_directionTokens (directions : List AxisDirection) :
    output (directions.map NormalizedToken.direction) =
      (repeatDirections 1152 directions).map NormalizedToken.direction := by
  induction directions with
  | nil => rfl
  | cons direction directions induction =>
      change List.replicate 1152 (.direction direction) ++
          output (directions.map NormalizedToken.direction) =
        (List.replicate 1152 direction ++
          repeatDirections 1152 directions).map NormalizedToken.direction
      rw [induction, List.map_append, List.map_replicate]

/-- Each route-delimited input word becomes its exact 1152-fold direction
expansion followed by the same delimiter. -/
@[simp] theorem output_delimitedDirections
    (directions : List AxisDirection) :
    output (directions.map NormalizedToken.direction ++ [.routeEnd]) =
      (repeatDirections 1152 directions).map NormalizedToken.direction ++
        [.routeEnd] := by
  unfold output
  rw [List.flatMap_append]
  change output (directions.map NormalizedToken.direction) ++ [.routeEnd] = _
  rw [output_directionTokens]

/-- The fixed expansion is a finite block transducer and hence runs in
polynomial time. -/
noncomputable def outputComputableInPolyTime :
    TM2ComputableInPolyTime id id output := by
  change TM2ComputableInPolyTime id id
    (fun tokens : List Token => tokens.flatMap block)
  exact FiniteBlockTransducer.computableInPolyTime block

end FallbackPrefixDirectionScaling
end PeriodicEightOccurrenceSplit
end LeanTrominoes

end
