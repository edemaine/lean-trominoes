/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierNormalizedSourceKeyRankOrderedFieldData
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizedSourceKeyRankOrderedFieldLength

/-! # Direct-source normalized carrier field/rank alignment -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

attribute [local instance] directSourceVariableDecidableEqInstance

noncomputable def
    directSourceCarrierNormalizedSourceKeySelectedFields_length :=
  fun symbols =>
    CarrierNormalizedSourceKeyRankOrderedFields.selectedFieldsAtPeriod_length
      (routeDescriptorStreamGridSize
        (numericRouteDescriptors (directSourceFormula decider symbols)))
      (numericRouteDescriptors (directSourceFormula decider symbols))

end PeriodicCNFStripReduction
end LeanTrominoes
