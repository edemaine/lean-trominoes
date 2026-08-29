/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedRouteJoinTime
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendFallbackPrefixCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendFallbackSuffixQueryCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierFallbackPrefixCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierFallbackSuffixQueryCompiler
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler

/-! # Direct compilation of complete fallback-route direction words -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicThreeDM.NormalizationDirectionRequest.Batch

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalFallbackRouteDirectionStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Complete carrier fallback words obtained by joining each scaled retained
source prefix to its aligned retained-fan suffix. -/
def directSourceFinalCarrierFallbackRouteDirections
    (symbols : List encoding.Γ) : List NormalizedToken :=
  DelimitedRouteJoin.joined
    (directSourceFinalCarrierFallbackPrefixDirections decider symbols)
    (directSourceFinalCarrierFallbackSuffixDirections decider symbols)

/-- Complete bend fallback words obtained by joining each scaled retained
source prefix to its aligned retained-fan suffix. -/
def directSourceFinalBendFallbackRouteDirections
    (symbols : List encoding.Γ) : List NormalizedToken :=
  DelimitedRouteJoin.joined
    (directSourceFinalBendFallbackPrefixDirections decider symbols)
    (directSourceFinalBendFallbackSuffixDirections decider symbols)

/-- Direct source symbols compile to all complete retained-carrier fallback
direction words in polynomial time. -/
noncomputable def
    directSourceFinalCarrierFallbackRouteDirectionsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalCarrierFallbackRouteDirections decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ :=
      ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalCarrierFallbackRouteDirections
    exact DelimitedRouteJoin.joinedComputableInPolyTimeOf
      id
      (directSourceFinalCarrierFallbackPrefixDirections decider)
      (directSourceFinalCarrierFallbackSuffixDirections decider)
      (directSourceFinalCarrierFallbackPrefixDirectionsComputableInPolyTime
        decider)
      (directSourceFinalCarrierFallbackSuffixDirectionsComputableInPolyTime
        decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime id _

/-- Direct source symbols compile to all complete retained-bend fallback
direction words in polynomial time. -/
noncomputable def
    directSourceFinalBendFallbackRouteDirectionsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalBendFallbackRouteDirections decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ :=
      ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalBendFallbackRouteDirections
    exact DelimitedRouteJoin.joinedComputableInPolyTimeOf
      id
      (directSourceFinalBendFallbackPrefixDirections decider)
      (directSourceFinalBendFallbackSuffixDirections decider)
      (directSourceFinalBendFallbackPrefixDirectionsComputableInPolyTime
        decider)
      (directSourceFinalBendFallbackSuffixDirectionsComputableInPolyTime
        decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime id _

end LeanTrominoes.PeriodicCNFStripReduction

end
