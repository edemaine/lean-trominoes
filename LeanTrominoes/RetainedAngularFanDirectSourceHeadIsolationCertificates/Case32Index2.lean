/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanDirectSourceHeadIsolationCertificates.Case32Index2Slots0
import LeanTrominoes.RetainedAngularFanDirectSourceHeadIsolationCertificates.Case32Index2Slots1
import LeanTrominoes.RetainedAngularFanDirectSourceHeadIsolationCertificates.Case32Index2Slots2
import LeanTrominoes.RetainedAngularFanDirectSourceHeadIsolationCertificates.Case32Index2Slots3

namespace LeanTrominoes.PeriodicEightOccurrenceSplit

theorem directSourceHeadFreshIndexCheck_case32_2 :
    directSourceHeadFreshIndexCheck .routedClause ⟨2, by decide⟩ = true := by
  unfold directSourceHeadFreshIndexCheck
  apply (finiteAll_eq_true _).mpr
  intro slot
  fin_cases slot
  · exact directSourceHeadFreshSlot_case32_2_0
  · exact directSourceHeadFreshSlot_case32_2_1
  · exact directSourceHeadFreshSlot_case32_2_2
  · exact directSourceHeadFreshSlot_case32_2_3
  · exact directSourceHeadFreshSlot_case32_2_4
  · exact directSourceHeadFreshSlot_case32_2_5
  · exact directSourceHeadFreshSlot_case32_2_6
  · exact directSourceHeadFreshSlot_case32_2_7

end LeanTrominoes.PeriodicEightOccurrenceSplit
