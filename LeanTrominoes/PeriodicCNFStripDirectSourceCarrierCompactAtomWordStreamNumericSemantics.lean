/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierCompactAtomWordStreamData
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierNormalizedSourceKeyRankOrderedNodeWordSemantics
import LeanTrominoes.PeriodicOrthocrossingGuardedCarrierSourcePairCompactAtomWordSemantics

/-! # Direct-source semantics of globally ranked compact carrier words -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directCarrierCompactAtomWordSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

attribute [local instance] directSourceVariableDecidableEqInstance

/-- The direct physical compiler emits exactly one normalized compact carrier
atom word in each global stable carrier rank. -/
theorem directSourceCarrierCompactAtomWordTokens_eq_encode
    (symbols : List encoding.Γ) :
    directSourceCarrierCompactAtomWordTokens decider symbols =
      let formula := directSourceFormula decider symbols
      let descriptors := numericRouteDescriptors formula
      let period := routeDescriptorStreamGridSize descriptors
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod period descriptors).dedup
      let nodes := (CarrierRankGlobal.enumeration datums).map
        (fun entry => entry.1.identity.node)
      DelimitedBinaryWords.encode
        (GuardedCarrierSourcePairCompactAtomWords.wordsAtPeriod
          period nodes) := by
  unfold directSourceCarrierCompactAtomWordTokens
  rw [directSourceCarrierNormalizedRankedWordTokens_eq_nodes]
  dsimp only
  exact GuardedCarrierSourcePairCompactAtomWords.tokens_nodesAtPeriod _ _

end PeriodicCNFStripReduction
end LeanTrominoes

end
