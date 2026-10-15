/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceHeadIsolationIndexChecks

namespace LeanTrominoes.PeriodicEightOccurrenceSplit
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

theorem directSourceHeadFreshIndexCheck_case29_1 :
    directSourceHeadFreshIndexCheck (.duplicator .middle 1) ⟨1, by decide⟩ = true := by
  decide +kernel

end LeanTrominoes.PeriodicEightOccurrenceSplit
