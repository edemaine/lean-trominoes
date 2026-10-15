/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 6.1
-/
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceSameTargetChecks

namespace LeanTrominoes.PeriodicEightOccurrenceSplit
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

theorem crossoverSameTargetCheck_case12 : crossoverSameTargetCheck 12 = true := by
  decide +kernel

theorem crossoverSameTargetCheck_case13 : crossoverSameTargetCheck 13 = true := by
  decide +kernel

theorem crossoverSameTargetCheck_case14 : crossoverSameTargetCheck 14 = true := by
  decide +kernel

theorem crossoverSameTargetCheck_case15 : crossoverSameTargetCheck 15 = true := by
  decide +kernel

end LeanTrominoes.PeriodicEightOccurrenceSplit
