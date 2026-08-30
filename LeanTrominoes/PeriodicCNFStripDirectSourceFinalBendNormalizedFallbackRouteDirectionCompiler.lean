/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoundedDelimitedDirectionCancellationCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendPreCancellationRouteDirectionCompiler

/-! # Direct compilation of normalized bend fallback-route words -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicThreeDM.NormalizationDirectionRequest.Batch

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Complete bend fallback words after bounded source/fan junction
cancellation. -/
def directSourceFinalBendNormalizedFallbackRouteDirections
    (symbols : List encoding.Γ) : List NormalizedToken :=
  BoundedDelimitedDirectionCancellation.output
    (directSourceFinalBendPreCancellationRouteDirections decider symbols)

/-- Direct source symbols compile to the junction-normalized bend fallback
word family in polynomial time. -/
noncomputable def
    directSourceFinalBendNormalizedFallbackRouteDirectionsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalBendNormalizedFallbackRouteDirections decider) := by
  unfold directSourceFinalBendNormalizedFallbackRouteDirections
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalBendPreCancellationRouteDirectionsComputableInPolyTime
      decider)
    BoundedDelimitedDirectionCancellation.outputComputableInPolyTime

end LeanTrominoes.PeriodicCNFStripReduction

end
