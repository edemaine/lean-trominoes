/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanDirectSourceHeadIsolationCertificates.Case32Index1Slots0
import LeanTrominoes.RetainedAngularFanDirectSourceHeadIsolationCertificates.Case32Index1Slots1
import LeanTrominoes.RetainedAngularFanDirectSourceHeadIsolationCertificates.Case32Index1Slots2
import LeanTrominoes.RetainedAngularFanDirectSourceHeadIsolationCertificates.Case32Index1Slots3

namespace LeanTrominoes.PeriodicEightOccurrenceSplit

theorem directSourceHeadFreshIndexCheck_case32_1 :
    directSourceHeadFreshIndexCheck .routedClause ⟨1, by decide⟩ = true := by
  unfold directSourceHeadFreshIndexCheck
  apply (finiteAll_eq_true _).mpr
  intro slot
  fin_cases slot
  · exact directSourceHeadFreshSlot_case32_1_0
  · exact directSourceHeadFreshSlot_case32_1_1
  · exact directSourceHeadFreshSlot_case32_1_2
  · exact directSourceHeadFreshSlot_case32_1_3
  · exact directSourceHeadFreshSlot_case32_1_4
  · exact directSourceHeadFreshSlot_case32_1_5
  · exact directSourceHeadFreshSlot_case32_1_6
  · exact directSourceHeadFreshSlot_case32_1_7

end LeanTrominoes.PeriodicEightOccurrenceSplit
