/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierFallbackPrefixTrimmer
import LeanTrominoes.RetainedAngularFanFallbackPrefixDirectionScalingCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Scaling compiled retained carrier fallback prefixes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace CarrierFallbackPrefixScaling

open Computability Turing Gadget
open CarrierSpanRouteDirections
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit

/-- Route-delimited fixed-clearance expansion of one unscaled source-prefix
word. -/
def scaledDelimitedDirections (directions : List AxisDirection) : List Token :=
  delimitedDirections (repeatDirections 1152 directions)

/-- Four explicitly scaled source-prefix words for one retained carrier. -/
def canonicalScaledPrefixBlock
    (horizontal : Bool) (span : Nat) : List Token :=
  scaledDelimitedDirections
      (carrierLensRoutePrefixDirections horizontal span 0 0) ++
    scaledDelimitedDirections
      (carrierLensRoutePrefixDirections horizontal span 0 1) ++
    scaledDelimitedDirections
      (carrierLensRoutePrefixDirections horizontal span 1 0) ++
    scaledDelimitedDirections
      (carrierLensRoutePrefixDirections horizontal span 1 1)

def output (tokens : List Token) : List Token :=
  FallbackPrefixDirectionScaling.output
    (CarrierFallbackPrefixTrimmer.output tokens)

/-- Trimming and fixed expansion recover the four explicit 1152-scaled
carrier source-prefix words. -/
@[simp] theorem output_canonicalBlock
    (horizontal : Bool) (span : Nat) (large : 6 < span) :
    output (canonicalBlock horizontal span) =
      canonicalScaledPrefixBlock horizontal span := by
  unfold output
  rw [CarrierFallbackPrefixTrimmer.output_canonicalBlock
    horizontal span large]
  unfold CarrierFallbackPrefixTrimmer.canonicalPrefixBlock
    canonicalScaledPrefixBlock scaledDelimitedDirections
  rw [FallbackPrefixDirectionScaling.output_append,
    FallbackPrefixDirectionScaling.output_append,
    FallbackPrefixDirectionScaling.output_append]
  unfold delimitedDirections directionTokens
  rw [
    FallbackPrefixDirectionScaling.output_delimitedDirections,
    FallbackPrefixDirectionScaling.output_delimitedDirections,
    FallbackPrefixDirectionScaling.output_delimitedDirections,
    FallbackPrefixDirectionScaling.output_delimitedDirections]

/-- A valid canonical carrier block resets both stages before the remaining
stream, so every later retained carrier is scaled independently. -/
theorem output_canonicalBlock_append
    (horizontal : Bool) (span : Nat) (large : 6 < span)
    (rest : List Token) :
    output (canonicalBlock horizontal span ++ rest) =
      canonicalScaledPrefixBlock horizontal span ++ output rest := by
  have blockEq := output_canonicalBlock horizontal span large
  unfold output at blockEq ⊢
  have scaledPrefixEq :
      FallbackPrefixDirectionScaling.output
          (CarrierFallbackPrefixTrimmer.canonicalPrefixBlock
            horizontal span) =
        canonicalScaledPrefixBlock horizontal span :=
    (congrArg FallbackPrefixDirectionScaling.output
      (CarrierFallbackPrefixTrimmer.output_canonicalBlock
        horizontal span large)).symm.trans blockEq
  rw [CarrierFallbackPrefixTrimmer.output_canonicalBlock_append
      horizontal span large rest,
    FallbackPrefixDirectionScaling.output_append,
    scaledPrefixEq]

/-- The carrier trimmer followed by fixed prefix scaling remains
polynomial-time computable. -/
noncomputable def outputComputableInPolyTime :
    TM2ComputableInPolyTime id id output := by
  let trimmed := CarrierFallbackPrefixTrimmer.outputComputableInPolyTime
  let scaled := TM2CompositionMachine.computableInPolyTime trimmed
    FallbackPrefixDirectionScaling.outputComputableInPolyTime
  change TM2ComputableInPolyTime id id
    (fun tokens => FallbackPrefixDirectionScaling.output
      (CarrierFallbackPrefixTrimmer.output tokens))
  exact scaled

end CarrierFallbackPrefixScaling
end PeriodicOrthocrossing
end LeanTrominoes

end
