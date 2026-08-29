/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedRouteJoinSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierFallbackPrefixScalingCompiler

/-! # Stream semantics of scaled retained-carrier fallback prefixes -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierFallbackPrefixScaling

open Gadget CarrierSpanRouteDirections
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- The four undelimited, fixed-clearance source-prefix words belonging to
one retained carrier. -/
def canonicalScaledPrefixWords
    (horizontal : Bool) (span : Nat) : List (List AxisDirection) :=
  [repeatDirections 1152
      (carrierLensRoutePrefixDirections horizontal span 0 0),
    repeatDirections 1152
      (carrierLensRoutePrefixDirections horizontal span 0 1),
    repeatDirections 1152
      (carrierLensRoutePrefixDirections horizontal span 1 0),
    repeatDirections 1152
      (carrierLensRoutePrefixDirections horizontal span 1 1)]

@[simp] theorem canonicalScaledPrefixWords_length
    (horizontal : Bool) (span : Nat) :
    (canonicalScaledPrefixWords horizontal span).length = 4 := by
  rfl

/-- Delimiting and flattening the four semantic words recovers the scaled
compiler block exactly. -/
theorem canonicalScaledPrefixBlock_eq_flatMap_delimited
    (horizontal : Bool) (span : Nat) :
    canonicalScaledPrefixBlock horizontal span =
      (canonicalScaledPrefixWords horizontal span).flatMap
        DelimitedRouteJoin.delimited := by
  have scaledDelimitedEq (directions : List AxisDirection) :
      scaledDelimitedDirections directions =
        DelimitedRouteJoin.delimited
          (repeatDirections 1152 directions) := by
    rfl
  unfold canonicalScaledPrefixBlock canonicalScaledPrefixWords
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [scaledDelimitedEq, scaledDelimitedEq, scaledDelimitedEq,
    scaledDelimitedEq]
  simp only [List.append_assoc]

/-- Scaling distributes over any stream of valid canonical carrier blocks.
The validity hypothesis is exactly the trimmer's span threshold. -/
theorem output_flatMap_canonicalBlocks
    (blocks : List (Bool × Nat))
    (large : ∀ block ∈ blocks, 6 < block.2) :
    output (blocks.flatMap fun block =>
        canonicalBlock block.1 block.2) =
      blocks.flatMap fun block =>
        canonicalScaledPrefixBlock block.1 block.2 := by
  induction blocks with
  | nil => rfl
  | cons block blocks induction =>
      simp only [List.flatMap_cons]
      rw [output_canonicalBlock_append block.1 block.2
        (large block (by simp))]
      rw [induction (fun rest restMember =>
        large rest (by simp [restMember]))]

end CarrierFallbackPrefixScaling
end LeanTrominoes.PeriodicOrthocrossing
