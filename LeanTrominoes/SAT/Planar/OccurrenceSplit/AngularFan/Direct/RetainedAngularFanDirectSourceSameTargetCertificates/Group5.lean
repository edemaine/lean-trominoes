/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 6.1
-/
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceSameTargetChecks

namespace LeanTrominoes.PeriodicEightOccurrenceSplit
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

theorem crossoverSameTargetCheck_case20 : crossoverSameTargetCheck 20 = true := by
  decide +kernel

theorem crossoverSameTargetCheck_case21 : crossoverSameTargetCheck 21 = true := by
  decide +kernel

theorem crossoverSameTargetCheck_case22 : crossoverSameTargetCheck 22 = true := by
  decide +kernel

theorem crossoverSameTargetCheck_case23 : crossoverSameTargetCheck 23 = true := by
  decide +kernel

end LeanTrominoes.PeriodicEightOccurrenceSplit
