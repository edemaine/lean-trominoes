/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCoordinatedOccurrenceStableRank
import LeanTrominoes.RetainedAngularOccurrenceGlobalTerminalComparisonScaling

/-! # Unscaling final coordinated terminal comparisons -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

/-- The exact final source-scaled strict terminal comparison stream is the
unscaled coordinated-source stream. -/
theorem retainedFinalCoordinatedGlobalTerminalStrictLowerBits_eq_unscaled
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (certificate :
      RetainedOccurrenceTerminalCertificate
        (finalCoordinatedSource formula).erase
        (finalCoordinatedSourceRoutes formula)) :
    retainedOccurrenceGlobalTerminalStrictLowerBits
        (retainedFinalCoordinatedScaledSource formula).erase
        (retainedFinalCoordinatedScaledSourceRoutes formula) =
      retainedOccurrenceGlobalTerminalStrictLowerBits
        (finalCoordinatedSource formula).erase
        (finalCoordinatedSourceRoutes formula) := by
  unfold retainedFinalCoordinatedScaledSource
    retainedFinalCoordinatedScaledSourceRoutes
  rw [PositionedPeriodicCNF.erase_scale]
  exact
    retainedOccurrenceGlobalTerminalStrictLowerBits_scaleIncidenceRoutes
      (finalCoordinatedSource formula).erase
      (finalCoordinatedSourceRoutes formula)
      certificate retainedAngularFanSourceClearanceFactor_pos

/-- The exact final source-scaled terminal equality stream is the unscaled
coordinated-source stream. -/
theorem retainedFinalCoordinatedGlobalTerminalEqualityBits_eq_unscaled
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (certificate :
      RetainedOccurrenceTerminalCertificate
        (finalCoordinatedSource formula).erase
        (finalCoordinatedSourceRoutes formula)) :
    retainedOccurrenceGlobalTerminalEqualityBits
        (retainedFinalCoordinatedScaledSource formula).erase
        (retainedFinalCoordinatedScaledSourceRoutes formula) =
      retainedOccurrenceGlobalTerminalEqualityBits
        (finalCoordinatedSource formula).erase
        (finalCoordinatedSourceRoutes formula) := by
  unfold retainedFinalCoordinatedScaledSource
    retainedFinalCoordinatedScaledSourceRoutes
  rw [PositionedPeriodicCNF.erase_scale]
  exact
    retainedOccurrenceGlobalTerminalEqualityBits_scaleIncidenceRoutes
      (finalCoordinatedSource formula).erase
      (finalCoordinatedSourceRoutes formula)
      certificate retainedAngularFanSourceClearanceFactor_pos

end PeriodicOrthocrossing
end LeanTrominoes
