/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceHeadIsolationData

namespace LeanTrominoes.PeriodicEightOccurrenceSplit
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

theorem directSourceHeadFreshCheck_case8 : directSourceHeadFreshCheck (.crossover 8) = true := by
  decide +kernel

theorem directSourceHeadFreshCheck_case9 : directSourceHeadFreshCheck (.crossover 9) = true := by
  decide +kernel

theorem directSourceHeadFreshCheck_case10 : directSourceHeadFreshCheck (.crossover 10) = true := by
  decide +kernel

theorem directSourceHeadFreshCheck_case11 : directSourceHeadFreshCheck (.crossover 11) = true := by
  decide +kernel

end LeanTrominoes.PeriodicEightOccurrenceSplit
