/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceHeadIsolationData

namespace LeanTrominoes.PeriodicEightOccurrenceSplit
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

theorem directSourceHeadFreshCheck_case24 : directSourceHeadFreshCheck (.crossover 24) = true := by
  decide +kernel

theorem directSourceHeadFreshCheck_case25 : directSourceHeadFreshCheck (.crossover 25) = true := by
  decide +kernel

theorem directSourceHeadFreshCheck_case26 : directSourceHeadFreshCheck (.duplicator .left 0) = true := by
  decide +kernel

theorem directSourceHeadFreshCheck_case27 : directSourceHeadFreshCheck (.duplicator .left 1) = true := by
  decide +kernel

end LeanTrominoes.PeriodicEightOccurrenceSplit
