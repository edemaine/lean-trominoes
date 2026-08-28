/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierNormalizedSourceKeyRankOrderedWordStreamNumericSemantics

/-! # Direct ranked normalized carrier words indexed by physical nodes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directNormalizedRankedNodeWordStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

attribute [local instance] directSourceVariableDecidableEqInstance

theorem datumPairs_eq_nodePairs
    (period : Nat) (entries : List (CarrierNodeRankDatum × Nat)) :
    entries.map
        (CarrierNodeNormalizedSourceKeys.datumPairAtPeriod period ∘ Prod.fst) =
      (entries.map (fun entry => entry.1.identity.node)).map
        (CarrierNodeNormalizedSourceKeys.pairAtPeriod period) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro entry _entryMember
  rfl

/-- The ranked pair stream is equivalently the period-normalized pair of an
explicit physical carrier-node list in global stable order. -/
theorem directSourceCarrierNormalizedRankedWordTokens_eq_nodes
    (symbols : List encoding.Γ) :
    directSourceCarrierNormalizedSourceKeyRankOrderedWordTokens
        decider symbols =
      let formula := directSourceFormula decider symbols
      let descriptors := numericRouteDescriptors formula
      let period := routeDescriptorStreamGridSize descriptors
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod period descriptors).dedup
      let nodes := (CarrierRankGlobal.enumeration datums).map
        (fun entry => entry.1.identity.node)
      DelimitedBinaryWords.encode
        (CarrierSourcePairFieldFormatter.words
          (nodes.map
            (CarrierNodeNormalizedSourceKeys.pairAtPeriod period))) := by
  rw [directSourceCarrierNormalizedSourceKeyRankOrderedWordTokens_eq_encode]
  dsimp only
  apply congrArg
    (fun pairs => DelimitedBinaryWords.encode
      (CarrierSourcePairFieldFormatter.words pairs))
  exact datumPairs_eq_nodePairs _ _

end PeriodicCNFStripReduction
end LeanTrominoes

end
