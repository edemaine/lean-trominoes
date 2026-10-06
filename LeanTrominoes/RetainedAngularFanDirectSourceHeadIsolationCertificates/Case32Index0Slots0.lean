/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanDirectSourceHeadIsolationIndexChecks

namespace LeanTrominoes.PeriodicEightOccurrenceSplit
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

theorem directSourceHeadFreshSlot_case32_0_0 :
    routeHeadGeometricallyFresh
      ((retainedDirectSourceZeroChoice .routedClause ⟨0, by decide⟩).completeFigure7Route ⟨0, by decide⟩) = true := by
  decide +kernel

theorem directSourceHeadFreshSlot_case32_0_1 :
    routeHeadGeometricallyFresh
      ((retainedDirectSourceZeroChoice .routedClause ⟨0, by decide⟩).completeFigure7Route ⟨1, by decide⟩) = true := by
  decide +kernel

end LeanTrominoes.PeriodicEightOccurrenceSplit
