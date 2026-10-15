/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 6.1
-/
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceSameTargetChecks

namespace LeanTrominoes.PeriodicEightOccurrenceSplit
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

theorem duplicatorSameTargetCheck_middle0 : duplicatorSameTargetCheck .middle 0 = true := by
  decide +kernel

theorem duplicatorSameTargetCheck_middle1 : duplicatorSameTargetCheck .middle 1 = true := by
  decide +kernel

theorem duplicatorSameTargetCheck_right0 : duplicatorSameTargetCheck .right 0 = true := by
  decide +kernel

theorem duplicatorSameTargetCheck_right1 : duplicatorSameTargetCheck .right 1 = true := by
  decide +kernel

end LeanTrominoes.PeriodicEightOccurrenceSplit
