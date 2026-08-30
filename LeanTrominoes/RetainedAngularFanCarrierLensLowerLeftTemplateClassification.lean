/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanCarrierLensTemplateRouteData

/-! # Terminal classification of the lower-left carrier route -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing

theorem carrierLensLowerLeftTemplateRoute_classified
    (horizontal : Bool) (span : Nat) :
    retainedTerminalDirectionClassify
        (PeriodicThreeSATThree.routeTerminalVector
          (carrierLensRawTemplateRoute horizontal span 1 0)) =
      some (carrierLensTemplateTerminalData horizontal span 1 0) := by
  cases horizontal
  · change retainedTerminalDirectionClassify (-1, 0) =
      some (.compass .west, 1)
    native_decide
  · change retainedTerminalDirectionClassify (0, 1) =
      some (.compass .south, 1)
    native_decide

end PeriodicEightOccurrenceSplit
end LeanTrominoes
