/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierRouteDirectionCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierFallbackPrefixScalingCompiler

/-! # Direct compilation of scaled carrier fallback prefixes -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierFallbackPrefixCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Fixed-clearance source-prefix words of every retained carrier, with one
route delimiter after each of its four local routes. -/
def directSourceFinalCarrierFallbackPrefixDirections
    (symbols : List encoding.Γ) :
    List CarrierSpanRouteDirections.Token :=
  CarrierFallbackPrefixScaling.output
    (directSourceCarrierRouteDirectionBlocks decider symbols)

/-- The complete scaled carrier prefix stream is polynomial-time computable
from direct PSPACE source symbols. -/
noncomputable def
    directSourceFinalCarrierFallbackPrefixDirectionsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalCarrierFallbackPrefixDirections decider) := by
  unfold directSourceFinalCarrierFallbackPrefixDirections
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceCarrierRouteDirectionBlocksComputableInPolyTime decider)
    CarrierFallbackPrefixScaling.outputComputableInPolyTime

end LeanTrominoes.PeriodicCNFStripReduction

end
