/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanCarrierLensTemplateRouteData

/-! # Terminal classification of the upper-right carrier route -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing

theorem carrierLensUpperRightTemplateRoute_classified
    (horizontal : Bool) (span : Nat) :
    retainedTerminalDirectionClassify
        (PeriodicThreeSATThree.routeTerminalVector
          (carrierLensRawTemplateRoute horizontal span 0 1)) =
      some (carrierLensTemplateTerminalData horizontal span 0 1) := by
  cases horizontal
  · rw [show PeriodicThreeSATThree.routeTerminalVector
        (carrierLensRawTemplateRoute false span 0 1) = (2, 0) by
      simp [carrierLensRawTemplateRoute,
        PeriodicThreeSATThree.routeTerminalVector, gridPolylineSegments,
        Cell.sub]]
    change retainedTerminalDirectionClassify (2, 0) =
      some (.compass .east, 2)
    native_decide
  · rw [show PeriodicThreeSATThree.routeTerminalVector
        (carrierLensRawTemplateRoute true span 0 1) = (0, -2) by
      simp [carrierLensRawTemplateRoute,
        PeriodicThreeSATThree.routeTerminalVector, gridPolylineSegments,
        Cell.sub]]
    change retainedTerminalDirectionClassify (0, -2) =
      some (.compass .north, 2)
    native_decide

end PeriodicEightOccurrenceSplit
end LeanTrominoes
