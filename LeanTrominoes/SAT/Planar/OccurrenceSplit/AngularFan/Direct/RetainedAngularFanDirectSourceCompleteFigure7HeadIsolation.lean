/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceHeadIsolationCertificates.Group0
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceHeadIsolationCertificates.Group1
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceHeadIsolationCertificates.Group2
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceHeadIsolationCertificates.Group3
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceHeadIsolationCertificates.Group4
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceHeadIsolationCertificates.Group5
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceHeadIsolationCertificates.Group6
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceHeadIsolationCertificates.Group7
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceHeadIsolationCertificates.Group8

/-! # Source-head isolation of the finite direct-source Figure 7 atlas -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

theorem directSourceHeadFreshCheck_correct (kind : RetainedDirectClauseKind) :
    directSourceHeadFreshCheck kind = true := by
  cases kind with
  | crossover index =>
    fin_cases index
    · exact directSourceHeadFreshCheck_case0
    · exact directSourceHeadFreshCheck_case1
    · exact directSourceHeadFreshCheck_case2
    · exact directSourceHeadFreshCheck_case3
    · exact directSourceHeadFreshCheck_case4
    · exact directSourceHeadFreshCheck_case5
    · exact directSourceHeadFreshCheck_case6
    · exact directSourceHeadFreshCheck_case7
    · exact directSourceHeadFreshCheck_case8
    · exact directSourceHeadFreshCheck_case9
    · exact directSourceHeadFreshCheck_case10
    · exact directSourceHeadFreshCheck_case11
    · exact directSourceHeadFreshCheck_case12
    · exact directSourceHeadFreshCheck_case13
    · exact directSourceHeadFreshCheck_case14
    · exact directSourceHeadFreshCheck_case15
    · exact directSourceHeadFreshCheck_case16
    · exact directSourceHeadFreshCheck_case17
    · exact directSourceHeadFreshCheck_case18
    · exact directSourceHeadFreshCheck_case19
    · exact directSourceHeadFreshCheck_case20
    · exact directSourceHeadFreshCheck_case21
    · exact directSourceHeadFreshCheck_case22
    · exact directSourceHeadFreshCheck_case23
    · exact directSourceHeadFreshCheck_case24
    · exact directSourceHeadFreshCheck_case25
  | duplicator arm index =>
    cases arm with
    | left =>
      fin_cases index
      · exact directSourceHeadFreshCheck_case26
      · exact directSourceHeadFreshCheck_case27
    | middle =>
      fin_cases index
      · exact directSourceHeadFreshCheck_case28
      · exact directSourceHeadFreshCheck_case29
    | right =>
      fin_cases index
      · exact directSourceHeadFreshCheck_case30
      · exact directSourceHeadFreshCheck_case31
  | routedClause => exact directSourceHeadFreshCheck_case32

/-- Every origin-zero direct-source Figure 7 route passes the compact
segment-level source-head isolation test. -/
theorem retainedDirectSourceZeroCompleteFigure7Route_headFresh_checked :
    ∀ (kind : RetainedDirectClauseKind)
      (index : Fin (retainedDirectSourcePrefixChoices kind).length)
      (slot : RetainedTerminalSlot),
      routeHeadGeometricallyFresh
          ((retainedDirectSourceZeroChoice kind index).completeFigure7Route
            slot) = true := by
  intro kind index slot
  have checked := directSourceHeadFreshCheck_correct kind
  simp only [directSourceHeadFreshCheck, finiteAll_eq_true] at checked
  exact checked index slot

/-- Every origin-zero direct-source Figure 7 route retains an isolated
source endpoint after unit subdivision. -/
theorem retainedDirectSourceZeroCompleteFigure7Route_headNotInTail
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (slot : RetainedTerminalSlot) :
    AxisDirection.HeadNotInTail
      (AxisDirection.unitSubdividePolyline
        ((retainedDirectSourceZeroChoice kind index).completeFigure7Route
          slot)) := by
  exact
    headNotInTail_unitSubdividePolyline_of_routeHeadGeometricallyFresh
      (retainedDirectSourceZeroCompleteFigure7Route_valid
        kind index slot).2
      (retainedDirectSourceZeroCompleteFigure7Route_headFresh_checked
        kind index slot)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
