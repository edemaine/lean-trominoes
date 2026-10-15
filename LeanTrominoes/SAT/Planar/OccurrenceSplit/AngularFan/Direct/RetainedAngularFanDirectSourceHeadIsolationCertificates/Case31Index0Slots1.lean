/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceHeadIsolationIndexChecks

namespace LeanTrominoes.PeriodicEightOccurrenceSplit
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

theorem directSourceHeadFreshSlot_case31_0_2 :
    routeHeadGeometricallyFresh
      ((retainedDirectSourceZeroChoice (.duplicator .right 1) ⟨0, by decide⟩).completeFigure7Route ⟨2, by decide⟩) = true := by
  decide +kernel

theorem directSourceHeadFreshSlot_case31_0_3 :
    routeHeadGeometricallyFresh
      ((retainedDirectSourceZeroChoice (.duplicator .right 1) ⟨0, by decide⟩).completeFigure7Route ⟨3, by decide⟩) = true := by
  decide +kernel

end LeanTrominoes.PeriodicEightOccurrenceSplit
