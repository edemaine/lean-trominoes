/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierNormalizedSourceKeyRankOrderedFieldNumericSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierNormalizedSourceKeyRankOrderedWordStreamData
import LeanTrominoes.PeriodicOrthocrossingCarrierSourcePairFieldFormatterStreamSemantics

/-! # Direct-source semantics of normalized ranked carrier words -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directNormalizedRankedWordSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

attribute [local instance] directSourceVariableDecidableEqInstance

/-- Formatting the direct ranked field column yields exactly one normalized
source-pair word for each carrier datum in global rank order. -/
theorem directSourceCarrierNormalizedSourceKeyRankOrderedWordTokens_eq_encode
    (symbols : List encoding.Γ) :
    directSourceCarrierNormalizedSourceKeyRankOrderedWordTokens
        decider symbols =
      let formula := directSourceFormula decider symbols
      let descriptors := numericRouteDescriptors formula
      let period := routeDescriptorStreamGridSize descriptors
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod period descriptors).dedup
      let sourcePairs := (CarrierRankGlobal.enumeration datums).map
        (CarrierNodeNormalizedSourceKeys.datumPairAtPeriod period ∘ Prod.fst)
      DelimitedBinaryWords.encode
        (CarrierSourcePairFieldFormatter.words sourcePairs) := by
  let formula := directSourceFormula decider symbols
  let descriptors := numericRouteDescriptors formula
  let period := routeDescriptorStreamGridSize descriptors
  let datums :=
    (routeDescriptorCarrierRankDatumsAtPeriod period descriptors).dedup
  let sourcePairs := (CarrierRankGlobal.enumeration datums).map
    (CarrierNodeNormalizedSourceKeys.datumPairAtPeriod period ∘ Prod.fst)
  have fieldsEq :
      directSourceCarrierNormalizedSourceKeyRankOrderedFields
          decider symbols =
        sourcePairs.flatMap fun sourcePair =>
          CarrierSourceKeyRepresentativeFieldLookup.sourcePairFields
            (some sourcePair) := by
    simpa [formula, descriptors, period, datums, sourcePairs,
      List.flatMap_map, Function.comp_def] using
      directSourceCarrierNormalizedSourceKeyRankOrderedFields_numeric
        decider symbols
  have formattedEq := congrArg
    (fun fields => CarrierSourcePairFieldFormatter.output
      (UnaryFieldEncoderMachine.unaryFields fields)) fieldsEq
  unfold directSourceCarrierNormalizedSourceKeyRankOrderedWordTokens
  rw [formattedEq]
  exact CarrierSourcePairFieldFormatter.output_sourcePairs sourcePairs

end PeriodicCNFStripReduction
end LeanTrominoes

end
