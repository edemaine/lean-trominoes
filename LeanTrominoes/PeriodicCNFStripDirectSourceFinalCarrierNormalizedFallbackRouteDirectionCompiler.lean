/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedRouteJoinTime
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierFallbackPrefixCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierNormalizedFallbackSuffixCompiler
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler

/-! # Direct compilation of normalized carrier fallback-route words -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicThreeDM.NormalizationDirectionRequest.Batch

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierNormalizedFallbackRouteStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Complete carrier fallback words formed from each scaled source prefix
and its aligned normalized retained-fan suffix. -/
def directSourceFinalCarrierNormalizedFallbackRouteDirections
    (symbols : List encoding.Γ) : List NormalizedToken :=
  DelimitedRouteJoin.joined
    (directSourceFinalCarrierFallbackPrefixDirections decider symbols)
    (directSourceFinalCarrierNormalizedFallbackSuffixDirections
      decider symbols)

/-- Direct source symbols compile to the complete normalized carrier
fallback word family in polynomial time. -/
noncomputable def
    directSourceFinalCarrierNormalizedFallbackRouteDirectionsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalCarrierNormalizedFallbackRouteDirections decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ :=
      ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalCarrierNormalizedFallbackRouteDirections
    exact DelimitedRouteJoin.joinedComputableInPolyTimeOf
      id
      (directSourceFinalCarrierFallbackPrefixDirections decider)
      (directSourceFinalCarrierNormalizedFallbackSuffixDirections decider)
      (directSourceFinalCarrierFallbackPrefixDirectionsComputableInPolyTime
        decider)
      (directSourceFinalCarrierNormalizedFallbackSuffixDirectionsComputableInPolyTime
        decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime id _

end LeanTrominoes.PeriodicCNFStripReduction

end
