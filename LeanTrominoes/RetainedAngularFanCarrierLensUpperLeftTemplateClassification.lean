/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanCarrierLensTemplateRouteData

/-! # Terminal classification of the upper-left carrier route -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing

theorem carrierLensUpperLeftTemplateRoute_classified
    (horizontal : Bool) (span : Nat) :
    retainedTerminalDirectionClassify
        (PeriodicThreeSATThree.routeTerminalVector
          (carrierLensRawTemplateRoute horizontal span 0 0)) =
      some (carrierLensTemplateTerminalData horizontal span 0 0) := by
  cases horizontal
  · change retainedTerminalDirectionClassify (0, 3) =
      some (.compass .south, 3)
    native_decide
  · change retainedTerminalDirectionClassify (3, 0) =
      some (.compass .east, 3)
    native_decide

end PeriodicEightOccurrenceSplit
end LeanTrominoes
