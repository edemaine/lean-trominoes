/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 6.1
-/
import LeanTrominoes.RetainedAngularFanDirectSourceCrossClauseCertificateData

/-! Kernel certificates for exceptional cross-clause pairs with different target centers. -/
namespace LeanTrominoes.PeriodicEightOccurrenceSplit
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

theorem crossoverOtherTargetsCheck_case0 :
    crossoverOtherTargetsCheck 0 = true := by
  decide +kernel

theorem crossoverOtherTargetsCheck_case1 :
    crossoverOtherTargetsCheck 1 = true := by
  decide +kernel

theorem crossoverOtherTargetsCheck_case2 :
    crossoverOtherTargetsCheck 2 = true := by
  decide +kernel

theorem crossoverOtherTargetsCheck_case3 :
    crossoverOtherTargetsCheck 3 = true := by
  decide +kernel

theorem crossoverOtherTargetsCheck_case4 :
    crossoverOtherTargetsCheck 4 = true := by
  decide +kernel

theorem crossoverOtherTargetsCheck_case5 :
    crossoverOtherTargetsCheck 5 = true := by
  decide +kernel

theorem crossoverOtherTargetsCheck_case6 :
    crossoverOtherTargetsCheck 6 = true := by
  decide +kernel

theorem crossoverOtherTargetsCheck_case7 :
    crossoverOtherTargetsCheck 7 = true := by
  decide +kernel

theorem crossoverOtherTargetsCheck_case8 :
    crossoverOtherTargetsCheck 8 = true := by
  decide +kernel

theorem crossoverOtherTargetsCheck_case9 :
    crossoverOtherTargetsCheck 9 = true := by
  decide +kernel

theorem crossoverOtherTargetsCheck_case10 :
    crossoverOtherTargetsCheck 10 = true := by
  decide +kernel

theorem crossoverOtherTargetsCheck_case11 :
    crossoverOtherTargetsCheck 11 = true := by
  decide +kernel

theorem crossoverOtherTargetsCheck_case12 :
    crossoverOtherTargetsCheck 12 = true := by
  decide +kernel

theorem crossoverOtherTargetsCheck_case13 :
    crossoverOtherTargetsCheck 13 = true := by
  decide +kernel

theorem crossoverOtherTargetsCheck_case14 :
    crossoverOtherTargetsCheck 14 = true := by
  decide +kernel

theorem crossoverOtherTargetsCheck_case15 :
    crossoverOtherTargetsCheck 15 = true := by
  decide +kernel

theorem crossoverOtherTargetsCheck_case16 :
    crossoverOtherTargetsCheck 16 = true := by
  decide +kernel

theorem crossoverOtherTargetsCheck_case17 :
    crossoverOtherTargetsCheck 17 = true := by
  decide +kernel

theorem crossoverOtherTargetsCheck_case18 :
    crossoverOtherTargetsCheck 18 = true := by
  decide +kernel

theorem crossoverOtherTargetsCheck_case19 :
    crossoverOtherTargetsCheck 19 = true := by
  decide +kernel

theorem crossoverOtherTargetsCheck_case20 :
    crossoverOtherTargetsCheck 20 = true := by
  decide +kernel

theorem crossoverOtherTargetsCheck_case21 :
    crossoverOtherTargetsCheck 21 = true := by
  decide +kernel

theorem crossoverOtherTargetsCheck_case22 :
    crossoverOtherTargetsCheck 22 = true := by
  decide +kernel

theorem crossoverOtherTargetsCheck_case23 :
    crossoverOtherTargetsCheck 23 = true := by
  decide +kernel

theorem crossoverOtherTargetsCheck_case24 :
    crossoverOtherTargetsCheck 24 = true := by
  decide +kernel

theorem crossoverOtherTargetsCheck_case25 :
    crossoverOtherTargetsCheck 25 = true := by
  decide +kernel

theorem crossoverOtherTargetsCheck_correct (index : Fin 26) :
    crossoverOtherTargetsCheck index = true := by
  fin_cases index
  · exact crossoverOtherTargetsCheck_case0
  · exact crossoverOtherTargetsCheck_case1
  · exact crossoverOtherTargetsCheck_case2
  · exact crossoverOtherTargetsCheck_case3
  · exact crossoverOtherTargetsCheck_case4
  · exact crossoverOtherTargetsCheck_case5
  · exact crossoverOtherTargetsCheck_case6
  · exact crossoverOtherTargetsCheck_case7
  · exact crossoverOtherTargetsCheck_case8
  · exact crossoverOtherTargetsCheck_case9
  · exact crossoverOtherTargetsCheck_case10
  · exact crossoverOtherTargetsCheck_case11
  · exact crossoverOtherTargetsCheck_case12
  · exact crossoverOtherTargetsCheck_case13
  · exact crossoverOtherTargetsCheck_case14
  · exact crossoverOtherTargetsCheck_case15
  · exact crossoverOtherTargetsCheck_case16
  · exact crossoverOtherTargetsCheck_case17
  · exact crossoverOtherTargetsCheck_case18
  · exact crossoverOtherTargetsCheck_case19
  · exact crossoverOtherTargetsCheck_case20
  · exact crossoverOtherTargetsCheck_case21
  · exact crossoverOtherTargetsCheck_case22
  · exact crossoverOtherTargetsCheck_case23
  · exact crossoverOtherTargetsCheck_case24
  · exact crossoverOtherTargetsCheck_case25

theorem duplicatorOtherTargetsCheck_left0 :
    duplicatorOtherTargetsCheck .left 0 = true := by
  decide +kernel

theorem duplicatorOtherTargetsCheck_left1 :
    duplicatorOtherTargetsCheck .left 1 = true := by
  decide +kernel

theorem duplicatorOtherTargetsCheck_middle0 :
    duplicatorOtherTargetsCheck .middle 0 = true := by
  decide +kernel

theorem duplicatorOtherTargetsCheck_middle1 :
    duplicatorOtherTargetsCheck .middle 1 = true := by
  decide +kernel

theorem duplicatorOtherTargetsCheck_right0 :
    duplicatorOtherTargetsCheck .right 0 = true := by
  decide +kernel

theorem duplicatorOtherTargetsCheck_right1 :
    duplicatorOtherTargetsCheck .right 1 = true := by
  decide +kernel

theorem duplicatorOtherTargetsCheck_correct (arm : PlanarThreeSAT.DuplicatorArm)
    (index : Fin 2) : duplicatorOtherTargetsCheck arm index = true := by
  cases arm with
  | left =>
      fin_cases index
      · exact duplicatorOtherTargetsCheck_left0
      · exact duplicatorOtherTargetsCheck_left1
  | middle =>
      fin_cases index
      · exact duplicatorOtherTargetsCheck_middle0
      · exact duplicatorOtherTargetsCheck_middle1
  | right =>
      fin_cases index
      · exact duplicatorOtherTargetsCheck_right0
      · exact duplicatorOtherTargetsCheck_right1

end LeanTrominoes.PeriodicEightOccurrenceSplit
