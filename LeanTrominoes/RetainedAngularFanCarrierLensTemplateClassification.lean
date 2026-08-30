/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanCarrierLensLowerLeftTemplateClassification
import LeanTrominoes.RetainedAngularFanCarrierLensLowerRightTemplateClassification
import LeanTrominoes.RetainedAngularFanCarrierLensUpperLeftTemplateClassification
import LeanTrominoes.RetainedAngularFanCarrierLensUpperRightTemplateClassification

/-! # Terminal classification of canonical carrier-lens routes -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing

theorem carrierLensTemplateRoute_classified
    (horizontal : Bool)
    (span : Nat)
    (spanLarge : 8 ≤ span)
    (localClauseIndex literalIndex : Fin 2) :
    retainedTerminalDirectionClassify
        (PeriodicThreeSATThree.routeTerminalVector
          (carrierLensRawTemplateRoute horizontal span
            localClauseIndex literalIndex)) =
      some (carrierLensTemplateTerminalData
        horizontal span
        localClauseIndex literalIndex) := by
  rcases localClauseIndex with ⟨(_ | _ | localClauseIndex), localClauseIndexLt⟩ <;>
    rcases literalIndex with ⟨(_ | _ | literalIndex), literalIndexLt⟩
  · exact carrierLensUpperLeftTemplateRoute_classified horizontal span
  · exact carrierLensUpperRightTemplateRoute_classified horizontal span
  · omega
  · exact carrierLensLowerLeftTemplateRoute_classified horizontal span
  · exact carrierLensLowerRightTemplateRoute_classified
      horizontal span spanLarge
  all_goals omega

end PeriodicEightOccurrenceSplit
end LeanTrominoes
