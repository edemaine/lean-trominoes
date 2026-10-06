/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 6.1
-/
import LeanTrominoes.RetainedAngularFanDirectSourceSameTargetCertificates.Group0
import LeanTrominoes.RetainedAngularFanDirectSourceSameTargetCertificates.Group1
import LeanTrominoes.RetainedAngularFanDirectSourceSameTargetCertificates.Group2
import LeanTrominoes.RetainedAngularFanDirectSourceSameTargetCertificates.Group3
import LeanTrominoes.RetainedAngularFanDirectSourceSameTargetCertificates.Group4
import LeanTrominoes.RetainedAngularFanDirectSourceSameTargetCertificates.Group5
import LeanTrominoes.RetainedAngularFanDirectSourceSameTargetCertificates.Group6
import LeanTrominoes.RetainedAngularFanDirectSourceSameTargetCertificates.Group7

/-! Aggregate kernel certificates for ordered incidences sharing a target. -/
namespace LeanTrominoes.PeriodicEightOccurrenceSplit

theorem crossoverSameTargetCheck_correct (index : Fin 26) : crossoverSameTargetCheck index = true := by
  fin_cases index
  · exact crossoverSameTargetCheck_case0
  · exact crossoverSameTargetCheck_case1
  · exact crossoverSameTargetCheck_case2
  · exact crossoverSameTargetCheck_case3
  · exact crossoverSameTargetCheck_case4
  · exact crossoverSameTargetCheck_case5
  · exact crossoverSameTargetCheck_case6
  · exact crossoverSameTargetCheck_case7
  · exact crossoverSameTargetCheck_case8
  · exact crossoverSameTargetCheck_case9
  · exact crossoverSameTargetCheck_case10
  · exact crossoverSameTargetCheck_case11
  · exact crossoverSameTargetCheck_case12
  · exact crossoverSameTargetCheck_case13
  · exact crossoverSameTargetCheck_case14
  · exact crossoverSameTargetCheck_case15
  · exact crossoverSameTargetCheck_case16
  · exact crossoverSameTargetCheck_case17
  · exact crossoverSameTargetCheck_case18
  · exact crossoverSameTargetCheck_case19
  · exact crossoverSameTargetCheck_case20
  · exact crossoverSameTargetCheck_case21
  · exact crossoverSameTargetCheck_case22
  · exact crossoverSameTargetCheck_case23
  · exact crossoverSameTargetCheck_case24
  · exact crossoverSameTargetCheck_case25







theorem duplicatorSameTargetCheck_correct (arm : PlanarThreeSAT.DuplicatorArm) (index : Fin 2) :
    duplicatorSameTargetCheck arm index = true := by
  cases arm with
  | left =>
    fin_cases index
    · exact duplicatorSameTargetCheck_left0
    · exact duplicatorSameTargetCheck_left1
  | middle =>
    fin_cases index
    · exact duplicatorSameTargetCheck_middle0
    · exact duplicatorSameTargetCheck_middle1
  | right =>
    fin_cases index
    · exact duplicatorSameTargetCheck_right0
    · exact duplicatorSameTargetCheck_right1

end LeanTrominoes.PeriodicEightOccurrenceSplit
