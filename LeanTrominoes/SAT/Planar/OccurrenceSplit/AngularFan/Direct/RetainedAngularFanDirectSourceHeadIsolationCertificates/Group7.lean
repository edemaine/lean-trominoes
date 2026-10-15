/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceHeadIsolationCertificates.Case28Index0
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceHeadIsolationCertificates.Case28Index1
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceHeadIsolationCertificates.Case29Index0
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceHeadIsolationCertificates.Case29Index1
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceHeadIsolationCertificates.Case30Index0
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceHeadIsolationCertificates.Case30Index1
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceHeadIsolationCertificates.Case31Index0
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceHeadIsolationCertificates.Case31Index1

namespace LeanTrominoes.PeriodicEightOccurrenceSplit

theorem directSourceHeadFreshCheck_case28 : directSourceHeadFreshCheck (.duplicator .middle 0) = true := by
  change (finiteAll (directSourceHeadFreshIndexCheck (.duplicator .middle 0))) = true
  apply (finiteAll_eq_true _).mpr
  intro index
  fin_cases index
  · exact directSourceHeadFreshIndexCheck_case28_0
  · exact directSourceHeadFreshIndexCheck_case28_1

theorem directSourceHeadFreshCheck_case29 : directSourceHeadFreshCheck (.duplicator .middle 1) = true := by
  change (finiteAll (directSourceHeadFreshIndexCheck (.duplicator .middle 1))) = true
  apply (finiteAll_eq_true _).mpr
  intro index
  fin_cases index
  · exact directSourceHeadFreshIndexCheck_case29_0
  · exact directSourceHeadFreshIndexCheck_case29_1

theorem directSourceHeadFreshCheck_case30 : directSourceHeadFreshCheck (.duplicator .right 0) = true := by
  change (finiteAll (directSourceHeadFreshIndexCheck (.duplicator .right 0))) = true
  apply (finiteAll_eq_true _).mpr
  intro index
  fin_cases index
  · exact directSourceHeadFreshIndexCheck_case30_0
  · exact directSourceHeadFreshIndexCheck_case30_1

theorem directSourceHeadFreshCheck_case31 : directSourceHeadFreshCheck (.duplicator .right 1) = true := by
  change (finiteAll (directSourceHeadFreshIndexCheck (.duplicator .right 1))) = true
  apply (finiteAll_eq_true _).mpr
  intro index
  fin_cases index
  · exact directSourceHeadFreshIndexCheck_case31_0
  · exact directSourceHeadFreshIndexCheck_case31_1

end LeanTrominoes.PeriodicEightOccurrenceSplit
