/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceNormalizedFormula
import LeanTrominoes.PeriodicCNFStripDirectSourceVariableDecidableEqInstance
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorEnumerationData
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizedSourceKeyRepresentativeFieldLookupData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalData

/-! # Direct-source normalized carrier representative fields -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

attribute [local instance] directSourceVariableDecidableEqInstance

abbrev directSourceCarrierNormalizedSourceKeySelectedFields
    (symbols : List encoding.Γ) : List Nat :=
  let descriptors :=
    numericRouteDescriptors (directSourceFormula decider symbols)
  let period := routeDescriptorStreamGridSize descriptors
  CarrierNormalizedSourceKeyRepresentativeFieldLookup.selectedFieldsAtPeriod
    period descriptors

@[simp] theorem directSourceCarrierNormalizedSourceKeySelectedFields_eq
    (symbols : List encoding.Γ) :
    directSourceCarrierNormalizedSourceKeySelectedFields decider symbols =
      CarrierNormalizedSourceKeyRepresentativeFieldLookup.selectedFieldsAtPeriod
        (routeDescriptorStreamGridSize
          (numericRouteDescriptors (directSourceFormula decider symbols)))
        (numericRouteDescriptors (directSourceFormula decider symbols)) := by
  rfl

end PeriodicCNFStripReduction
end LeanTrominoes

end
