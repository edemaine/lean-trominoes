/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 6.1
-/
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceSameTargetChecks

namespace LeanTrominoes.PeriodicEightOccurrenceSplit
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

theorem crossoverSameTargetCheck_case4 : crossoverSameTargetCheck 4 = true := by
  decide +kernel

theorem crossoverSameTargetCheck_case5 : crossoverSameTargetCheck 5 = true := by
  decide +kernel

theorem crossoverSameTargetCheck_case6 : crossoverSameTargetCheck 6 = true := by
  decide +kernel

theorem crossoverSameTargetCheck_case7 : crossoverSameTargetCheck 7 = true := by
  decide +kernel

end LeanTrominoes.PeriodicEightOccurrenceSplit
