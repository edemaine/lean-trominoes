/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierNormalizedSourceKeyRepresentativeFieldData
import LeanTrominoes.PeriodicCNFStripDirectSourceVariableDecidableEqInstance
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalData
import LeanTrominoes.UnaryPermutationRankBlockLookupData

/-! # Direct-source normalized carrier fields in global rank order -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

attribute [local instance] directSourceVariableDecidableEqInstance

abbrev directSourceCarrierGlobalRanks
    (symbols : List encoding.Γ) : List Nat :=
  CarrierRankGlobal.ranks
    (numericRouteDescriptors (directSourceFormula decider symbols))

/-- The normalized source-key fields of each retained carrier identity,
permuted into its global stable carrier rank. -/
def directSourceCarrierNormalizedSourceKeyRankOrderedFields
    (symbols : List encoding.Γ) : List Nat :=
  UnaryPermutationRankBlockLookup.values
    CarrierSourceKeyRepresentativeFieldLookup.fieldCount
    (directSourceCarrierGlobalRanks decider symbols)
    (directSourceCarrierNormalizedSourceKeySelectedFields decider symbols)

@[simp] theorem directSourceCarrierNormalizedSourceKeyRankOrderedFields_eq
    (symbols : List encoding.Γ) :
    directSourceCarrierNormalizedSourceKeyRankOrderedFields decider symbols =
      UnaryPermutationRankBlockLookup.values
        CarrierSourceKeyRepresentativeFieldLookup.fieldCount
        (CarrierRankGlobal.ranks
          (directSourceFormula decider symbols).numericRouteDescriptors)
        (CarrierNormalizedSourceKeyRepresentativeFieldLookup.selectedFieldsAtPeriod
          (routeDescriptorStreamGridSize
            (directSourceFormula decider symbols).numericRouteDescriptors)
          (directSourceFormula decider symbols).numericRouteDescriptors) := by
  rfl

theorem directSourceCarrierNormalizedSourceKeyRankOrderedFields_encoded_eq
    (symbols : List encoding.Γ) :
    UnaryFieldEncoderMachine.unaryFields
        (UnaryPermutationRankBlockLookup.values
          CarrierSourceKeyRepresentativeFieldLookup.fieldCount
          (CarrierRankGlobal.ranks
            (directSourceFormula decider symbols).numericRouteDescriptors)
          (CarrierNormalizedSourceKeyRepresentativeFieldLookup.selectedFieldsAtPeriod
            (routeDescriptorStreamGridSize
              (directSourceFormula decider symbols).numericRouteDescriptors)
            (directSourceFormula decider symbols).numericRouteDescriptors)) =
      UnaryFieldEncoderMachine.unaryFields
        (directSourceCarrierNormalizedSourceKeyRankOrderedFields
          decider symbols) :=
  congrArg UnaryFieldEncoderMachine.unaryFields
    (directSourceCarrierNormalizedSourceKeyRankOrderedFields_eq
      decider symbols).symm

end PeriodicCNFStripReduction
end LeanTrominoes

end
