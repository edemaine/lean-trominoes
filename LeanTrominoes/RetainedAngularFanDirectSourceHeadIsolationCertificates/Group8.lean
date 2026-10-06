/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanDirectSourceHeadIsolationCertificates.Case32Index0
import LeanTrominoes.RetainedAngularFanDirectSourceHeadIsolationCertificates.Case32Index1
import LeanTrominoes.RetainedAngularFanDirectSourceHeadIsolationCertificates.Case32Index2

namespace LeanTrominoes.PeriodicEightOccurrenceSplit

theorem directSourceHeadFreshCheck_case32 : directSourceHeadFreshCheck .routedClause = true := by
  change (finiteAll (directSourceHeadFreshIndexCheck .routedClause)) = true
  apply (finiteAll_eq_true _).mpr
  intro index
  fin_cases index
  · exact directSourceHeadFreshIndexCheck_case32_0
  · exact directSourceHeadFreshIndexCheck_case32_1
  · exact directSourceHeadFreshIndexCheck_case32_2

end LeanTrominoes.PeriodicEightOccurrenceSplit
