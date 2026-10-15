/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 6.1
-/
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceSameTargetChecks

namespace LeanTrominoes.PeriodicEightOccurrenceSplit
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

theorem crossoverSameTargetCheck_case24 : crossoverSameTargetCheck 24 = true := by
  decide +kernel

theorem crossoverSameTargetCheck_case25 : crossoverSameTargetCheck 25 = true := by
  decide +kernel

theorem duplicatorSameTargetCheck_left0 : duplicatorSameTargetCheck .left 0 = true := by
  decide +kernel

theorem duplicatorSameTargetCheck_left1 : duplicatorSameTargetCheck .left 1 = true := by
  decide +kernel

end LeanTrominoes.PeriodicEightOccurrenceSplit
