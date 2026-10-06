/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanDirectSourceHeadIsolationData

namespace LeanTrominoes.PeriodicEightOccurrenceSplit
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

theorem directSourceHeadFreshCheck_case0 : directSourceHeadFreshCheck (.crossover 0) = true := by
  decide +kernel

theorem directSourceHeadFreshCheck_case1 : directSourceHeadFreshCheck (.crossover 1) = true := by
  decide +kernel

theorem directSourceHeadFreshCheck_case2 : directSourceHeadFreshCheck (.crossover 2) = true := by
  decide +kernel

theorem directSourceHeadFreshCheck_case3 : directSourceHeadFreshCheck (.crossover 3) = true := by
  decide +kernel

end LeanTrominoes.PeriodicEightOccurrenceSplit
