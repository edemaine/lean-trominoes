/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceHeadIsolationCertificates.Case32Index0Slots0
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceHeadIsolationCertificates.Case32Index0Slots1
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceHeadIsolationCertificates.Case32Index0Slots2
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceHeadIsolationCertificates.Case32Index0Slots3

namespace LeanTrominoes.PeriodicEightOccurrenceSplit

theorem directSourceHeadFreshIndexCheck_case32_0 :
    directSourceHeadFreshIndexCheck .routedClause ⟨0, by decide⟩ = true := by
  unfold directSourceHeadFreshIndexCheck
  apply (finiteAll_eq_true _).mpr
  intro slot
  fin_cases slot
  · exact directSourceHeadFreshSlot_case32_0_0
  · exact directSourceHeadFreshSlot_case32_0_1
  · exact directSourceHeadFreshSlot_case32_0_2
  · exact directSourceHeadFreshSlot_case32_0_3
  · exact directSourceHeadFreshSlot_case32_0_4
  · exact directSourceHeadFreshSlot_case32_0_5
  · exact directSourceHeadFreshSlot_case32_0_6
  · exact directSourceHeadFreshSlot_case32_0_7

end LeanTrominoes.PeriodicEightOccurrenceSplit
