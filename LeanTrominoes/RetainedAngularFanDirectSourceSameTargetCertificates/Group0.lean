/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 6.1
-/
import LeanTrominoes.RetainedAngularFanDirectSourceSameTargetChecks

namespace LeanTrominoes.PeriodicEightOccurrenceSplit
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

theorem crossoverSameTargetCheck_case0 : crossoverSameTargetCheck 0 = true := by
  decide +kernel

theorem crossoverSameTargetCheck_case1 : crossoverSameTargetCheck 1 = true := by
  decide +kernel

theorem crossoverSameTargetCheck_case2 : crossoverSameTargetCheck 2 = true := by
  decide +kernel

theorem crossoverSameTargetCheck_case3 : crossoverSameTargetCheck 3 = true := by
  decide +kernel

end LeanTrominoes.PeriodicEightOccurrenceSplit
