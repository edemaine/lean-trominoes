/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanDirectSourceHeadIsolationData

namespace LeanTrominoes.PeriodicEightOccurrenceSplit
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

theorem directSourceHeadFreshCheck_case16 : directSourceHeadFreshCheck (.crossover 16) = true := by
  decide +kernel

theorem directSourceHeadFreshCheck_case17 : directSourceHeadFreshCheck (.crossover 17) = true := by
  decide +kernel

theorem directSourceHeadFreshCheck_case18 : directSourceHeadFreshCheck (.crossover 18) = true := by
  decide +kernel

theorem directSourceHeadFreshCheck_case19 : directSourceHeadFreshCheck (.crossover 19) = true := by
  decide +kernel

end LeanTrominoes.PeriodicEightOccurrenceSplit
