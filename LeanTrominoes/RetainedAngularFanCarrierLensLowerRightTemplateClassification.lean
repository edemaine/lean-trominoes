/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanCarrierLensTemplateRouteData

/-! # Terminal classification of the lower-right carrier route -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing

theorem carrierLensLowerRightTemplateRoute_classified
    (horizontal : Bool) (span : Nat)
    (spanLarge : 8 ≤ span) :
    retainedTerminalDirectionClassify
        (PeriodicThreeSATThree.routeTerminalVector
          (carrierLensRawTemplateRoute horizontal span 1 1)) =
      some (carrierLensTemplateTerminalData horizontal span 1 1) := by
  have spanSix : (6 : Int) < span := by exact_mod_cast (by omega : 6 < span)
  have spanNotLtSix : ¬(span : Int) < 6 := by omega
  have spanDiffNeZero : (span : Int) - 6 ≠ 0 := by omega
  cases horizontal <;>
    simp [carrierLensRawTemplateRoute, carrierLensTemplateTerminalData,
      PeriodicThreeSATThree.routeTerminalVector, gridPolylineSegments,
      retainedTerminalDirectionClassify, retainedRayClassify,
      terminalPort, compassLength, RetainedRay.terminalDirection,
      oppositePort, RetainedRay.length,
      Cell.sub, spanSix, spanNotLtSix, spanDiffNeZero]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
