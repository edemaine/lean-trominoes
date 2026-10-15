/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 6.1
-/
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceSameTargetChecks

namespace LeanTrominoes.PeriodicEightOccurrenceSplit
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

theorem crossoverSameTargetCheck_case16 : crossoverSameTargetCheck 16 = true := by
  decide +kernel

theorem crossoverSameTargetCheck_case17 : crossoverSameTargetCheck 17 = true := by
  decide +kernel

theorem crossoverSameTargetCheck_case18 : crossoverSameTargetCheck 18 = true := by
  decide +kernel

theorem crossoverSameTargetCheck_case19 : crossoverSameTargetCheck 19 = true := by
  decide +kernel

end LeanTrominoes.PeriodicEightOccurrenceSplit
