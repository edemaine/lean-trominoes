/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedRouteJoinTime
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendFallbackPrefixCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendNormalizedFallbackSuffixCompiler
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler

/-! # Direct compilation of bend words before junction cancellation -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicThreeDM.NormalizationDirectionRequest.Batch

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalBendPreCancellationRouteStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Bend fallback words formed from each scaled prefix and independently
normalized retained-fan suffix, before source/fan junction cancellation. -/
def directSourceFinalBendPreCancellationRouteDirections
    (symbols : List encoding.Γ) : List NormalizedToken :=
  DelimitedRouteJoin.joined
    (directSourceFinalBendFallbackPrefixDirections decider symbols)
    (directSourceFinalBendNormalizedFallbackSuffixDirections decider symbols)

noncomputable def
    directSourceFinalBendPreCancellationRouteDirectionsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalBendPreCancellationRouteDirections decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ :=
      ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalBendPreCancellationRouteDirections
    exact DelimitedRouteJoin.joinedComputableInPolyTimeOf
      id
      (directSourceFinalBendFallbackPrefixDirections decider)
      (directSourceFinalBendNormalizedFallbackSuffixDirections decider)
      (directSourceFinalBendFallbackPrefixDirectionsComputableInPolyTime
        decider)
      (directSourceFinalBendNormalizedFallbackSuffixDirectionsComputableInPolyTime
        decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime id _

end LeanTrominoes.PeriodicCNFStripReduction

end
