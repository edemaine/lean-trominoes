/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceHeadIsolationData

namespace LeanTrominoes.PeriodicEightOccurrenceSplit
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

theorem directSourceHeadFreshCheck_case4 : directSourceHeadFreshCheck (.crossover 4) = true := by
  decide +kernel

theorem directSourceHeadFreshCheck_case5 : directSourceHeadFreshCheck (.crossover 5) = true := by
  decide +kernel

theorem directSourceHeadFreshCheck_case6 : directSourceHeadFreshCheck (.crossover 6) = true := by
  decide +kernel

theorem directSourceHeadFreshCheck_case7 : directSourceHeadFreshCheck (.crossover 7) = true := by
  decide +kernel

end LeanTrominoes.PeriodicEightOccurrenceSplit
