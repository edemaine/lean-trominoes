/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceHeadIsolationData

namespace LeanTrominoes.PeriodicEightOccurrenceSplit
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

theorem directSourceHeadFreshCheck_case20 : directSourceHeadFreshCheck (.crossover 20) = true := by
  decide +kernel

theorem directSourceHeadFreshCheck_case21 : directSourceHeadFreshCheck (.crossover 21) = true := by
  decide +kernel

theorem directSourceHeadFreshCheck_case22 : directSourceHeadFreshCheck (.crossover 22) = true := by
  decide +kernel

theorem directSourceHeadFreshCheck_case23 : directSourceHeadFreshCheck (.crossover 23) = true := by
  decide +kernel

end LeanTrominoes.PeriodicEightOccurrenceSplit
