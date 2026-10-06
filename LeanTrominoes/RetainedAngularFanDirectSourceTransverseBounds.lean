/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanDirectSourceRouteChoice
import LeanTrominoes.RetainedAngularFanOuterRadialSeparation
import LeanTrominoes.ScaledPointNeighborhoodSeparation
import LeanTrominoes.OrthogonalPolylineStrictSeparationCheck
import Mathlib.Tactic.FinCases
import LeanTrominoes.RetainedAngularFanDirectSourceRouteHull

/-!
# Transverse bounds for direct source routes

The coordinated direct-source atlas changes the first fixed-length escape
of an outer fan but retains the same terminal ray and tail.  This file
records the finite transverse-envelope certificate needed to use a selected
direct route as a bounded replacement for the ordinary outer fan.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

private def routeBandCheck (normal center : Cell) (radius : Int) (route : List Cell) : Bool :=
  route.all fun point => decide (Cell.linearValue normal center - radius ≤
    Cell.linearValue normal point ∧ Cell.linearValue normal point ≤
      Cell.linearValue normal center + radius)

private def directBandCheck (kind : RetainedDirectClauseKind) (radius : Int) : Bool :=
  finiteAll fun index : Fin (retainedDirectSourcePrefixChoices kind).length =>
    finiteAll fun slot : RetainedTerminalSlot =>
      routeBandCheck
        (retainedTerminalFanOuterTransverseNormal (retainedDirectSourceFanTerminalAt kind index).1)
        (retainedDirectSourceFanCenterAt kind index) radius
        (retainedDirectSourceCompleteRouteHull kind index slot)

private def tailBandCheck (kind : RetainedDirectClauseKind) : Bool :=
  finiteAll fun index : Fin (retainedDirectSourcePrefixChoices kind).length =>
    finiteAll fun slot : RetainedTerminalSlot =>
      routeBandCheck
        (retainedTerminalFanOuterTransverseNormal (retainedDirectSourceFanTerminalAt kind index).1)
        (retainedDirectSourceFanCenterAt kind index) 845
        (retainedDirectSourceShiftedTailHull
          (retainedDirectSourceFanCenterAt kind index)
          (retainedDirectSourceFanTerminalAt kind index) slot)

private def tailRectangleCheck (kind : RetainedDirectClauseKind) : Bool :=
  finiteAll fun index : Fin (retainedDirectSourcePrefixChoices kind).length =>
    finiteAll fun slot : RetainedTerminalSlot =>
      let localSegment : GridSegment :=
        ⟨(retainedDirectSourceLocalRouteAt kind index).headD (0, 0),
          (retainedDirectSourceLocalRouteAt kind index).getLastD (0, 0)⟩
      (retainedDirectSourceShiftedTailHull
        (retainedDirectSourceFanCenterAt kind index)
        (retainedDirectSourceFanTerminalAt kind index) slot).all fun point =>
          decide (InClosedGridRectangle
            (coordinateRadiusLower 65 (Cell.scale (retainedTerminalFanTotalRefinement * 4)
              localSegment.coordinateLower))
            (coordinateRadiusUpper 65 (Cell.scale (retainedTerminalFanTotalRefinement * 4)
              localSegment.coordinateUpper)) point)

private def tightBandCheck (kind : RetainedDirectClauseKind) : Bool :=
  guardedCheck (kind ≠ .routedClause) (directBandCheck kind 495)

private theorem directBandCheck_correct_case0 :
    directBandCheck (.crossover 0) 3103 = true := by
  decide +kernel

private theorem directBandCheck_correct_case1 :
    directBandCheck (.crossover 1) 3103 = true := by
  decide +kernel

private theorem directBandCheck_correct_case2 :
    directBandCheck (.crossover 2) 3103 = true := by
  decide +kernel

private theorem directBandCheck_correct_case3 :
    directBandCheck (.crossover 3) 3103 = true := by
  decide +kernel

private theorem directBandCheck_correct_case4 :
    directBandCheck (.crossover 4) 3103 = true := by
  decide +kernel

private theorem directBandCheck_correct_case5 :
    directBandCheck (.crossover 5) 3103 = true := by
  decide +kernel

private theorem directBandCheck_correct_case6 :
    directBandCheck (.crossover 6) 3103 = true := by
  decide +kernel

private theorem directBandCheck_correct_case7 :
    directBandCheck (.crossover 7) 3103 = true := by
  decide +kernel

private theorem directBandCheck_correct_case8 :
    directBandCheck (.crossover 8) 3103 = true := by
  decide +kernel

private theorem directBandCheck_correct_case9 :
    directBandCheck (.crossover 9) 3103 = true := by
  decide +kernel

private theorem directBandCheck_correct_case10 :
    directBandCheck (.crossover 10) 3103 = true := by
  decide +kernel

private theorem directBandCheck_correct_case11 :
    directBandCheck (.crossover 11) 3103 = true := by
  decide +kernel

private theorem directBandCheck_correct_case12 :
    directBandCheck (.crossover 12) 3103 = true := by
  decide +kernel

private theorem directBandCheck_correct_case13 :
    directBandCheck (.crossover 13) 3103 = true := by
  decide +kernel

private theorem directBandCheck_correct_case14 :
    directBandCheck (.crossover 14) 3103 = true := by
  decide +kernel

private theorem directBandCheck_correct_case15 :
    directBandCheck (.crossover 15) 3103 = true := by
  decide +kernel

private theorem directBandCheck_correct_case16 :
    directBandCheck (.crossover 16) 3103 = true := by
  decide +kernel

private theorem directBandCheck_correct_case17 :
    directBandCheck (.crossover 17) 3103 = true := by
  decide +kernel

private theorem directBandCheck_correct_case18 :
    directBandCheck (.crossover 18) 3103 = true := by
  decide +kernel

private theorem directBandCheck_correct_case19 :
    directBandCheck (.crossover 19) 3103 = true := by
  decide +kernel

private theorem directBandCheck_correct_case20 :
    directBandCheck (.crossover 20) 3103 = true := by
  decide +kernel

private theorem directBandCheck_correct_case21 :
    directBandCheck (.crossover 21) 3103 = true := by
  decide +kernel

private theorem directBandCheck_correct_case22 :
    directBandCheck (.crossover 22) 3103 = true := by
  decide +kernel

private theorem directBandCheck_correct_case23 :
    directBandCheck (.crossover 23) 3103 = true := by
  decide +kernel

private theorem directBandCheck_correct_case24 :
    directBandCheck (.crossover 24) 3103 = true := by
  decide +kernel

private theorem directBandCheck_correct_case25 :
    directBandCheck (.crossover 25) 3103 = true := by
  decide +kernel

private theorem directBandCheck_correct_case26 :
    directBandCheck (.duplicator .left 0) 3103 = true := by
  decide +kernel

private theorem directBandCheck_correct_case27 :
    directBandCheck (.duplicator .left 1) 3103 = true := by
  decide +kernel

private theorem directBandCheck_correct_case28 :
    directBandCheck (.duplicator .middle 0) 3103 = true := by
  decide +kernel

private theorem directBandCheck_correct_case29 :
    directBandCheck (.duplicator .middle 1) 3103 = true := by
  decide +kernel

private theorem directBandCheck_correct_case30 :
    directBandCheck (.duplicator .right 0) 3103 = true := by
  decide +kernel

private theorem directBandCheck_correct_case31 :
    directBandCheck (.duplicator .right 1) 3103 = true := by
  decide +kernel

private theorem directBandCheck_correct_case32 :
    directBandCheck .routedClause 3103 = true := by
  decide +kernel

private theorem directBandCheck_correct (kind : RetainedDirectClauseKind) :
    directBandCheck kind 3103 = true := by
  cases kind with
  | crossover index =>
    fin_cases index
    · exact directBandCheck_correct_case0
    · exact directBandCheck_correct_case1
    · exact directBandCheck_correct_case2
    · exact directBandCheck_correct_case3
    · exact directBandCheck_correct_case4
    · exact directBandCheck_correct_case5
    · exact directBandCheck_correct_case6
    · exact directBandCheck_correct_case7
    · exact directBandCheck_correct_case8
    · exact directBandCheck_correct_case9
    · exact directBandCheck_correct_case10
    · exact directBandCheck_correct_case11
    · exact directBandCheck_correct_case12
    · exact directBandCheck_correct_case13
    · exact directBandCheck_correct_case14
    · exact directBandCheck_correct_case15
    · exact directBandCheck_correct_case16
    · exact directBandCheck_correct_case17
    · exact directBandCheck_correct_case18
    · exact directBandCheck_correct_case19
    · exact directBandCheck_correct_case20
    · exact directBandCheck_correct_case21
    · exact directBandCheck_correct_case22
    · exact directBandCheck_correct_case23
    · exact directBandCheck_correct_case24
    · exact directBandCheck_correct_case25
  | duplicator arm index =>
    cases arm with
    | left =>
      fin_cases index
      · exact directBandCheck_correct_case26
      · exact directBandCheck_correct_case27
    | middle =>
      fin_cases index
      · exact directBandCheck_correct_case28
      · exact directBandCheck_correct_case29
    | right =>
      fin_cases index
      · exact directBandCheck_correct_case30
      · exact directBandCheck_correct_case31
  | routedClause => exact directBandCheck_correct_case32

private theorem tailBandCheck_correct_case0 :
    tailBandCheck (.crossover 0) = true := by
  decide +kernel

private theorem tailBandCheck_correct_case1 :
    tailBandCheck (.crossover 1) = true := by
  decide +kernel

private theorem tailBandCheck_correct_case2 :
    tailBandCheck (.crossover 2) = true := by
  decide +kernel

private theorem tailBandCheck_correct_case3 :
    tailBandCheck (.crossover 3) = true := by
  decide +kernel

private theorem tailBandCheck_correct_case4 :
    tailBandCheck (.crossover 4) = true := by
  decide +kernel

private theorem tailBandCheck_correct_case5 :
    tailBandCheck (.crossover 5) = true := by
  decide +kernel

private theorem tailBandCheck_correct_case6 :
    tailBandCheck (.crossover 6) = true := by
  decide +kernel

private theorem tailBandCheck_correct_case7 :
    tailBandCheck (.crossover 7) = true := by
  decide +kernel

private theorem tailBandCheck_correct_case8 :
    tailBandCheck (.crossover 8) = true := by
  decide +kernel

private theorem tailBandCheck_correct_case9 :
    tailBandCheck (.crossover 9) = true := by
  decide +kernel

private theorem tailBandCheck_correct_case10 :
    tailBandCheck (.crossover 10) = true := by
  decide +kernel

private theorem tailBandCheck_correct_case11 :
    tailBandCheck (.crossover 11) = true := by
  decide +kernel

private theorem tailBandCheck_correct_case12 :
    tailBandCheck (.crossover 12) = true := by
  decide +kernel

private theorem tailBandCheck_correct_case13 :
    tailBandCheck (.crossover 13) = true := by
  decide +kernel

private theorem tailBandCheck_correct_case14 :
    tailBandCheck (.crossover 14) = true := by
  decide +kernel

private theorem tailBandCheck_correct_case15 :
    tailBandCheck (.crossover 15) = true := by
  decide +kernel

private theorem tailBandCheck_correct_case16 :
    tailBandCheck (.crossover 16) = true := by
  decide +kernel

private theorem tailBandCheck_correct_case17 :
    tailBandCheck (.crossover 17) = true := by
  decide +kernel

private theorem tailBandCheck_correct_case18 :
    tailBandCheck (.crossover 18) = true := by
  decide +kernel

private theorem tailBandCheck_correct_case19 :
    tailBandCheck (.crossover 19) = true := by
  decide +kernel

private theorem tailBandCheck_correct_case20 :
    tailBandCheck (.crossover 20) = true := by
  decide +kernel

private theorem tailBandCheck_correct_case21 :
    tailBandCheck (.crossover 21) = true := by
  decide +kernel

private theorem tailBandCheck_correct_case22 :
    tailBandCheck (.crossover 22) = true := by
  decide +kernel

private theorem tailBandCheck_correct_case23 :
    tailBandCheck (.crossover 23) = true := by
  decide +kernel

private theorem tailBandCheck_correct_case24 :
    tailBandCheck (.crossover 24) = true := by
  decide +kernel

private theorem tailBandCheck_correct_case25 :
    tailBandCheck (.crossover 25) = true := by
  decide +kernel

private theorem tailBandCheck_correct_case26 :
    tailBandCheck (.duplicator .left 0) = true := by
  decide +kernel

private theorem tailBandCheck_correct_case27 :
    tailBandCheck (.duplicator .left 1) = true := by
  decide +kernel

private theorem tailBandCheck_correct_case28 :
    tailBandCheck (.duplicator .middle 0) = true := by
  decide +kernel

private theorem tailBandCheck_correct_case29 :
    tailBandCheck (.duplicator .middle 1) = true := by
  decide +kernel

private theorem tailBandCheck_correct_case30 :
    tailBandCheck (.duplicator .right 0) = true := by
  decide +kernel

private theorem tailBandCheck_correct_case31 :
    tailBandCheck (.duplicator .right 1) = true := by
  decide +kernel

private theorem tailBandCheck_correct_case32 :
    tailBandCheck .routedClause = true := by
  decide +kernel

private theorem tailBandCheck_correct (kind : RetainedDirectClauseKind) :
    tailBandCheck kind = true := by
  cases kind with
  | crossover index =>
    fin_cases index
    · exact tailBandCheck_correct_case0
    · exact tailBandCheck_correct_case1
    · exact tailBandCheck_correct_case2
    · exact tailBandCheck_correct_case3
    · exact tailBandCheck_correct_case4
    · exact tailBandCheck_correct_case5
    · exact tailBandCheck_correct_case6
    · exact tailBandCheck_correct_case7
    · exact tailBandCheck_correct_case8
    · exact tailBandCheck_correct_case9
    · exact tailBandCheck_correct_case10
    · exact tailBandCheck_correct_case11
    · exact tailBandCheck_correct_case12
    · exact tailBandCheck_correct_case13
    · exact tailBandCheck_correct_case14
    · exact tailBandCheck_correct_case15
    · exact tailBandCheck_correct_case16
    · exact tailBandCheck_correct_case17
    · exact tailBandCheck_correct_case18
    · exact tailBandCheck_correct_case19
    · exact tailBandCheck_correct_case20
    · exact tailBandCheck_correct_case21
    · exact tailBandCheck_correct_case22
    · exact tailBandCheck_correct_case23
    · exact tailBandCheck_correct_case24
    · exact tailBandCheck_correct_case25
  | duplicator arm index =>
    cases arm with
    | left =>
      fin_cases index
      · exact tailBandCheck_correct_case26
      · exact tailBandCheck_correct_case27
    | middle =>
      fin_cases index
      · exact tailBandCheck_correct_case28
      · exact tailBandCheck_correct_case29
    | right =>
      fin_cases index
      · exact tailBandCheck_correct_case30
      · exact tailBandCheck_correct_case31
  | routedClause => exact tailBandCheck_correct_case32

private theorem tailRectangleCheck_correct_case0 :
    tailRectangleCheck (.crossover 0) = true := by
  decide +kernel

private theorem tailRectangleCheck_correct_case1 :
    tailRectangleCheck (.crossover 1) = true := by
  decide +kernel

private theorem tailRectangleCheck_correct_case2 :
    tailRectangleCheck (.crossover 2) = true := by
  decide +kernel

private theorem tailRectangleCheck_correct_case3 :
    tailRectangleCheck (.crossover 3) = true := by
  decide +kernel

private theorem tailRectangleCheck_correct_case4 :
    tailRectangleCheck (.crossover 4) = true := by
  decide +kernel

private theorem tailRectangleCheck_correct_case5 :
    tailRectangleCheck (.crossover 5) = true := by
  decide +kernel

private theorem tailRectangleCheck_correct_case6 :
    tailRectangleCheck (.crossover 6) = true := by
  decide +kernel

private theorem tailRectangleCheck_correct_case7 :
    tailRectangleCheck (.crossover 7) = true := by
  decide +kernel

private theorem tailRectangleCheck_correct_case8 :
    tailRectangleCheck (.crossover 8) = true := by
  decide +kernel

private theorem tailRectangleCheck_correct_case9 :
    tailRectangleCheck (.crossover 9) = true := by
  decide +kernel

private theorem tailRectangleCheck_correct_case10 :
    tailRectangleCheck (.crossover 10) = true := by
  decide +kernel

private theorem tailRectangleCheck_correct_case11 :
    tailRectangleCheck (.crossover 11) = true := by
  decide +kernel

private theorem tailRectangleCheck_correct_case12 :
    tailRectangleCheck (.crossover 12) = true := by
  decide +kernel

private theorem tailRectangleCheck_correct_case13 :
    tailRectangleCheck (.crossover 13) = true := by
  decide +kernel

private theorem tailRectangleCheck_correct_case14 :
    tailRectangleCheck (.crossover 14) = true := by
  decide +kernel

private theorem tailRectangleCheck_correct_case15 :
    tailRectangleCheck (.crossover 15) = true := by
  decide +kernel

private theorem tailRectangleCheck_correct_case16 :
    tailRectangleCheck (.crossover 16) = true := by
  decide +kernel

private theorem tailRectangleCheck_correct_case17 :
    tailRectangleCheck (.crossover 17) = true := by
  decide +kernel

private theorem tailRectangleCheck_correct_case18 :
    tailRectangleCheck (.crossover 18) = true := by
  decide +kernel

private theorem tailRectangleCheck_correct_case19 :
    tailRectangleCheck (.crossover 19) = true := by
  decide +kernel

private theorem tailRectangleCheck_correct_case20 :
    tailRectangleCheck (.crossover 20) = true := by
  decide +kernel

private theorem tailRectangleCheck_correct_case21 :
    tailRectangleCheck (.crossover 21) = true := by
  decide +kernel

private theorem tailRectangleCheck_correct_case22 :
    tailRectangleCheck (.crossover 22) = true := by
  decide +kernel

private theorem tailRectangleCheck_correct_case23 :
    tailRectangleCheck (.crossover 23) = true := by
  decide +kernel

private theorem tailRectangleCheck_correct_case24 :
    tailRectangleCheck (.crossover 24) = true := by
  decide +kernel

private theorem tailRectangleCheck_correct_case25 :
    tailRectangleCheck (.crossover 25) = true := by
  decide +kernel

private theorem tailRectangleCheck_correct_case26 :
    tailRectangleCheck (.duplicator .left 0) = true := by
  decide +kernel

private theorem tailRectangleCheck_correct_case27 :
    tailRectangleCheck (.duplicator .left 1) = true := by
  decide +kernel

private theorem tailRectangleCheck_correct_case28 :
    tailRectangleCheck (.duplicator .middle 0) = true := by
  decide +kernel

private theorem tailRectangleCheck_correct_case29 :
    tailRectangleCheck (.duplicator .middle 1) = true := by
  decide +kernel

private theorem tailRectangleCheck_correct_case30 :
    tailRectangleCheck (.duplicator .right 0) = true := by
  decide +kernel

private theorem tailRectangleCheck_correct_case31 :
    tailRectangleCheck (.duplicator .right 1) = true := by
  decide +kernel

private theorem tailRectangleCheck_correct_case32 :
    tailRectangleCheck .routedClause = true := by
  decide +kernel

private theorem tailRectangleCheck_correct (kind : RetainedDirectClauseKind) :
    tailRectangleCheck kind = true := by
  cases kind with
  | crossover index =>
    fin_cases index
    · exact tailRectangleCheck_correct_case0
    · exact tailRectangleCheck_correct_case1
    · exact tailRectangleCheck_correct_case2
    · exact tailRectangleCheck_correct_case3
    · exact tailRectangleCheck_correct_case4
    · exact tailRectangleCheck_correct_case5
    · exact tailRectangleCheck_correct_case6
    · exact tailRectangleCheck_correct_case7
    · exact tailRectangleCheck_correct_case8
    · exact tailRectangleCheck_correct_case9
    · exact tailRectangleCheck_correct_case10
    · exact tailRectangleCheck_correct_case11
    · exact tailRectangleCheck_correct_case12
    · exact tailRectangleCheck_correct_case13
    · exact tailRectangleCheck_correct_case14
    · exact tailRectangleCheck_correct_case15
    · exact tailRectangleCheck_correct_case16
    · exact tailRectangleCheck_correct_case17
    · exact tailRectangleCheck_correct_case18
    · exact tailRectangleCheck_correct_case19
    · exact tailRectangleCheck_correct_case20
    · exact tailRectangleCheck_correct_case21
    · exact tailRectangleCheck_correct_case22
    · exact tailRectangleCheck_correct_case23
    · exact tailRectangleCheck_correct_case24
    · exact tailRectangleCheck_correct_case25
  | duplicator arm index =>
    cases arm with
    | left =>
      fin_cases index
      · exact tailRectangleCheck_correct_case26
      · exact tailRectangleCheck_correct_case27
    | middle =>
      fin_cases index
      · exact tailRectangleCheck_correct_case28
      · exact tailRectangleCheck_correct_case29
    | right =>
      fin_cases index
      · exact tailRectangleCheck_correct_case30
      · exact tailRectangleCheck_correct_case31
  | routedClause => exact tailRectangleCheck_correct_case32

private theorem tightBandCheck_correct_case0 :
    tightBandCheck (.crossover 0) = true := by
  decide +kernel

private theorem tightBandCheck_correct_case1 :
    tightBandCheck (.crossover 1) = true := by
  decide +kernel

private theorem tightBandCheck_correct_case2 :
    tightBandCheck (.crossover 2) = true := by
  decide +kernel

private theorem tightBandCheck_correct_case3 :
    tightBandCheck (.crossover 3) = true := by
  decide +kernel

private theorem tightBandCheck_correct_case4 :
    tightBandCheck (.crossover 4) = true := by
  decide +kernel

private theorem tightBandCheck_correct_case5 :
    tightBandCheck (.crossover 5) = true := by
  decide +kernel

private theorem tightBandCheck_correct_case6 :
    tightBandCheck (.crossover 6) = true := by
  decide +kernel

private theorem tightBandCheck_correct_case7 :
    tightBandCheck (.crossover 7) = true := by
  decide +kernel

private theorem tightBandCheck_correct_case8 :
    tightBandCheck (.crossover 8) = true := by
  decide +kernel

private theorem tightBandCheck_correct_case9 :
    tightBandCheck (.crossover 9) = true := by
  decide +kernel

private theorem tightBandCheck_correct_case10 :
    tightBandCheck (.crossover 10) = true := by
  decide +kernel

private theorem tightBandCheck_correct_case11 :
    tightBandCheck (.crossover 11) = true := by
  decide +kernel

private theorem tightBandCheck_correct_case12 :
    tightBandCheck (.crossover 12) = true := by
  decide +kernel

private theorem tightBandCheck_correct_case13 :
    tightBandCheck (.crossover 13) = true := by
  decide +kernel

private theorem tightBandCheck_correct_case14 :
    tightBandCheck (.crossover 14) = true := by
  decide +kernel

private theorem tightBandCheck_correct_case15 :
    tightBandCheck (.crossover 15) = true := by
  decide +kernel

private theorem tightBandCheck_correct_case16 :
    tightBandCheck (.crossover 16) = true := by
  decide +kernel

private theorem tightBandCheck_correct_case17 :
    tightBandCheck (.crossover 17) = true := by
  decide +kernel

private theorem tightBandCheck_correct_case18 :
    tightBandCheck (.crossover 18) = true := by
  decide +kernel

private theorem tightBandCheck_correct_case19 :
    tightBandCheck (.crossover 19) = true := by
  decide +kernel

private theorem tightBandCheck_correct_case20 :
    tightBandCheck (.crossover 20) = true := by
  decide +kernel

private theorem tightBandCheck_correct_case21 :
    tightBandCheck (.crossover 21) = true := by
  decide +kernel

private theorem tightBandCheck_correct_case22 :
    tightBandCheck (.crossover 22) = true := by
  decide +kernel

private theorem tightBandCheck_correct_case23 :
    tightBandCheck (.crossover 23) = true := by
  decide +kernel

private theorem tightBandCheck_correct_case24 :
    tightBandCheck (.crossover 24) = true := by
  decide +kernel

private theorem tightBandCheck_correct_case25 :
    tightBandCheck (.crossover 25) = true := by
  decide +kernel

private theorem tightBandCheck_correct_case26 :
    tightBandCheck (.duplicator .left 0) = true := by
  decide +kernel

private theorem tightBandCheck_correct_case27 :
    tightBandCheck (.duplicator .left 1) = true := by
  decide +kernel

private theorem tightBandCheck_correct_case28 :
    tightBandCheck (.duplicator .middle 0) = true := by
  decide +kernel

private theorem tightBandCheck_correct_case29 :
    tightBandCheck (.duplicator .middle 1) = true := by
  decide +kernel

private theorem tightBandCheck_correct_case30 :
    tightBandCheck (.duplicator .right 0) = true := by
  decide +kernel

private theorem tightBandCheck_correct_case31 :
    tightBandCheck (.duplicator .right 1) = true := by
  decide +kernel

private theorem tightBandCheck_correct_case32 :
    tightBandCheck .routedClause = true := by
  decide +kernel

private theorem tightBandCheck_correct (kind : RetainedDirectClauseKind) :
    tightBandCheck kind = true := by
  cases kind with
  | crossover index =>
    fin_cases index
    · exact tightBandCheck_correct_case0
    · exact tightBandCheck_correct_case1
    · exact tightBandCheck_correct_case2
    · exact tightBandCheck_correct_case3
    · exact tightBandCheck_correct_case4
    · exact tightBandCheck_correct_case5
    · exact tightBandCheck_correct_case6
    · exact tightBandCheck_correct_case7
    · exact tightBandCheck_correct_case8
    · exact tightBandCheck_correct_case9
    · exact tightBandCheck_correct_case10
    · exact tightBandCheck_correct_case11
    · exact tightBandCheck_correct_case12
    · exact tightBandCheck_correct_case13
    · exact tightBandCheck_correct_case14
    · exact tightBandCheck_correct_case15
    · exact tightBandCheck_correct_case16
    · exact tightBandCheck_correct_case17
    · exact tightBandCheck_correct_case18
    · exact tightBandCheck_correct_case19
    · exact tightBandCheck_correct_case20
    · exact tightBandCheck_correct_case21
    · exact tightBandCheck_correct_case22
    · exact tightBandCheck_correct_case23
    · exact tightBandCheck_correct_case24
    · exact tightBandCheck_correct_case25
  | duplicator arm index =>
    cases arm with
    | left =>
      fin_cases index
      · exact tightBandCheck_correct_case26
      · exact tightBandCheck_correct_case27
    | middle =>
      fin_cases index
      · exact tightBandCheck_correct_case28
      · exact tightBandCheck_correct_case29
    | right =>
      fin_cases index
      · exact tightBandCheck_correct_case30
      · exact tightBandCheck_correct_case31
  | routedClause => exact tightBandCheck_correct_case32

/-- Every point of every local coordinated direct-source route lies in a
radius-3103 transverse band around its represented terminal line.  This
coarse certificate includes the unusually wide routed-clause escape. -/
theorem retainedDirectSourceFanCompleteRouteAt_transverse_band :
    ∀ (kind : RetainedDirectClauseKind)
      (index : Fin (retainedDirectSourcePrefixChoices kind).length)
      (slot : RetainedTerminalSlot)
      (point : Cell),
      point ∈
          retainedDirectSourceFanCompleteRouteAt kind index slot →
        Cell.linearValue
              (retainedTerminalFanOuterTransverseNormal
                (retainedDirectSourceFanTerminalAt kind index).1)
              (retainedDirectSourceFanCenterAt kind index) -
            3103 ≤
          Cell.linearValue
              (retainedTerminalFanOuterTransverseNormal
                (retainedDirectSourceFanTerminalAt kind index).1)
              point ∧
        Cell.linearValue
              (retainedTerminalFanOuterTransverseNormal
                (retainedDirectSourceFanTerminalAt kind index).1)
              point ≤
          Cell.linearValue
                (retainedTerminalFanOuterTransverseNormal
                  (retainedDirectSourceFanTerminalAt kind index).1)
                (retainedDirectSourceFanCenterAt kind index) +
            3103 := by
  intro kind index slot point member
  have checked := directBandCheck_correct kind
  simp only [directBandCheck, routeBandCheck, finiteAll_eq_true, List.all_eq_true, decide_eq_true_eq] at checked
  exact retainedDirectSourceCompleteRouteHull_linearBounds kind index slot _ _ _
    (checked index slot) member

/-- The shifted radial tail after every customized 64-block escape remains
in the ordinary radius-845 transverse corridor. -/
theorem retainedDirectSourceFanShiftedTailAt_transverse_band :
    ∀ (kind : RetainedDirectClauseKind)
      (index : Fin (retainedDirectSourcePrefixChoices kind).length)
      (slot : RetainedTerminalSlot)
      (point : Cell),
      point ∈
          retainedTerminalFanOuterEscapedShiftedTail
            (retainedDirectSourceFanCenterAt kind index)
            (retainedDirectSourceFanTerminalAt kind index)
            slot →
        Cell.linearValue
              (retainedTerminalFanOuterTransverseNormal
                (retainedDirectSourceFanTerminalAt kind index).1)
              (retainedDirectSourceFanCenterAt kind index) -
            845 ≤
          Cell.linearValue
              (retainedTerminalFanOuterTransverseNormal
                (retainedDirectSourceFanTerminalAt kind index).1)
              point ∧
        Cell.linearValue
              (retainedTerminalFanOuterTransverseNormal
                (retainedDirectSourceFanTerminalAt kind index).1)
              point ≤
          Cell.linearValue
                (retainedTerminalFanOuterTransverseNormal
                  (retainedDirectSourceFanTerminalAt kind index).1)
                (retainedDirectSourceFanCenterAt kind index) +
            845 := by
  intro kind index slot point member
  have checked := tailBandCheck_correct kind
  simp only [tailBandCheck, routeBandCheck, finiteAll_eq_true, List.all_eq_true, decide_eq_true_eq] at checked
  exact retainedDirectSourceShiftedTailHull_linearBounds _ _ _ slot _ _
    (checked index slot) member

/-- The same shifted radial tails remain in the radius-65 coordinate tube
around their fully refined represented source segments. -/
theorem
    retainedDirectSourceFanShiftedTailAt_point_in_scaledLocalSegmentRectangle :
    ∀ (kind : RetainedDirectClauseKind)
      (index : Fin (retainedDirectSourcePrefixChoices kind).length)
      (slot : RetainedTerminalSlot)
      (point : Cell),
      point ∈
          retainedTerminalFanOuterEscapedShiftedTail
            (retainedDirectSourceFanCenterAt kind index)
            (retainedDirectSourceFanTerminalAt kind index)
            slot →
        let localSegment : GridSegment :=
          ⟨(retainedDirectSourceLocalRouteAt kind index).headD (0, 0),
            (retainedDirectSourceLocalRouteAt kind index).getLastD (0, 0)⟩
        InClosedGridRectangle
          (coordinateRadiusLower 65
            (Cell.scale
              (retainedTerminalFanTotalRefinement * 4)
              localSegment.coordinateLower))
          (coordinateRadiusUpper 65
            (Cell.scale
              (retainedTerminalFanTotalRefinement * 4)
              localSegment.coordinateUpper))
          point := by
  intro kind index slot point member
  have checked := tailRectangleCheck_correct kind
  simp only [tailRectangleCheck, finiteAll_eq_true, List.all_eq_true, decide_eq_true_eq] at checked
  have hullBounds := checked index slot
  let center := retainedDirectSourceFanCenterAt kind index
  let terminal := retainedDirectSourceFanTerminalAt kind index
  let localSegment : GridSegment :=
    ⟨(retainedDirectSourceLocalRouteAt kind index).headD (0, 0),
      (retainedDirectSourceLocalRouteAt kind index).getLastD (0, 0)⟩
  let lower := coordinateRadiusLower 65
    (Cell.scale (retainedTerminalFanTotalRefinement * 4) localSegment.coordinateLower)
  let upper := coordinateRadiusUpper 65
    (Cell.scale (retainedTerminalFanTotalRefinement * 4) localSegment.coordinateUpper)
  have xBounds := retainedDirectSourceShiftedTailHull_linearBounds center (1, 0) terminal slot
    lower.1 upper.1 (fun p hp => by
      have h := hullBounds p hp
      simpa [Cell.linearValue, InClosedGridRectangle] using ⟨h.1, h.2.1⟩) member
  have yBounds := retainedDirectSourceShiftedTailHull_linearBounds center (0, 1) terminal slot
    lower.2 upper.2 (fun p hp => by
      have h := hullBounds p hp
      simpa [Cell.linearValue, InClosedGridRectangle] using ⟨h.2.2.1, h.2.2.2⟩) member
  change InClosedGridRectangle lower upper point
  exact ⟨by simpa [Cell.linearValue] using xBounds.1,
    by simpa [Cell.linearValue] using xBounds.2,
    by simpa [Cell.linearValue] using yBounds.1,
    by simpa [Cell.linearValue] using yBounds.2⟩

/-- Outside the routed-clause component, the finite direct-source atlas has
the much tighter radius-495 transverse envelope. -/
theorem
    retainedDirectSourceFanCompleteRouteAt_transverse_band_of_kind_ne_routedClause :
    ∀ (kind : RetainedDirectClauseKind)
      (index : Fin (retainedDirectSourcePrefixChoices kind).length)
      (slot : RetainedTerminalSlot)
      (_kindNe : kind ≠ .routedClause)
      (point : Cell),
      point ∈
          retainedDirectSourceFanCompleteRouteAt kind index slot →
        Cell.linearValue
              (retainedTerminalFanOuterTransverseNormal
                (retainedDirectSourceFanTerminalAt kind index).1)
              (retainedDirectSourceFanCenterAt kind index) -
            495 ≤
          Cell.linearValue
              (retainedTerminalFanOuterTransverseNormal
                (retainedDirectSourceFanTerminalAt kind index).1)
              point ∧
        Cell.linearValue
              (retainedTerminalFanOuterTransverseNormal
                (retainedDirectSourceFanTerminalAt kind index).1)
              point ≤
          Cell.linearValue
                (retainedTerminalFanOuterTransverseNormal
                  (retainedDirectSourceFanTerminalAt kind index).1)
                (retainedDirectSourceFanCenterAt kind index) +
            495 := by
  intro kind index slot different point member
  have checked := tightBandCheck_correct kind
  simp only [tightBandCheck, guardedCheck_eq_true, directBandCheck, routeBandCheck, finiteAll_eq_true, List.all_eq_true, decide_eq_true_eq] at checked
  exact retainedDirectSourceCompleteRouteHull_linearBounds kind index slot _ _ _
    (checked different index slot) member

/-- Translating a non-routed direct choice into physical component
coordinates preserves its radius-495 transverse envelope. -/
theorem
    RetainedDirectSourceRouteChoice.completeRoute_transverse_band_of_kind_ne_routedClause
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot)
    (kindNe : choice.kind ≠ .routedClause)
    {point : Cell}
    (pointMember : point ∈ choice.completeRoute slot) :
    Cell.linearValue
          (retainedTerminalFanOuterTransverseNormal
            (retainedDirectSourceFanTerminalAt
              choice.kind choice.index).1)
          (retainedDirectSourcePositionedFanCenterAt
            choice.origin choice.kind choice.index) -
        495 ≤
      Cell.linearValue
          (retainedTerminalFanOuterTransverseNormal
            (retainedDirectSourceFanTerminalAt
              choice.kind choice.index).1)
          point ∧
    Cell.linearValue
          (retainedTerminalFanOuterTransverseNormal
            (retainedDirectSourceFanTerminalAt
              choice.kind choice.index).1)
          point ≤
      Cell.linearValue
            (retainedTerminalFanOuterTransverseNormal
              (retainedDirectSourceFanTerminalAt
                choice.kind choice.index).1)
            (retainedDirectSourcePositionedFanCenterAt
              choice.origin choice.kind choice.index) +
        495 := by
  unfold RetainedDirectSourceRouteChoice.completeRoute
    retainedDirectSourcePositionedFanCompleteRouteAt
    PeriodicOrthocrossing.translatePolyline at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨localPoint, localPointMember, rfl⟩
  have localBound :=
    retainedDirectSourceFanCompleteRouteAt_transverse_band_of_kind_ne_routedClause
      choice.kind choice.index slot kindNe localPoint localPointMember
  unfold retainedDirectSourcePositionedFanCenterAt
  simp only [Cell.linearValue_add]
  constructor <;> omega

/-- Physical translation preserves the ordinary transverse envelope of every
direct choice's shifted radial tail. -/
theorem
    RetainedDirectSourceRouteChoice.shiftedTail_transverse_band
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot)
    {point : Cell}
    (pointMember :
      point ∈
        PeriodicOrthocrossing.translatePolyline
          (retainedDirectSourceFanPositioningOffset choice.origin)
          (retainedTerminalFanOuterEscapedShiftedTail
            (retainedDirectSourceFanCenterAt
              choice.kind choice.index)
            (retainedDirectSourceFanTerminalAt
              choice.kind choice.index)
            slot)) :
    Cell.linearValue
          (retainedTerminalFanOuterTransverseNormal
            (retainedDirectSourceFanTerminalAt
              choice.kind choice.index).1)
          (retainedDirectSourcePositionedFanCenterAt
            choice.origin choice.kind choice.index) -
        845 ≤
      Cell.linearValue
          (retainedTerminalFanOuterTransverseNormal
            (retainedDirectSourceFanTerminalAt
              choice.kind choice.index).1)
          point ∧
    Cell.linearValue
          (retainedTerminalFanOuterTransverseNormal
            (retainedDirectSourceFanTerminalAt
              choice.kind choice.index).1)
          point ≤
      Cell.linearValue
            (retainedTerminalFanOuterTransverseNormal
              (retainedDirectSourceFanTerminalAt
                choice.kind choice.index).1)
            (retainedDirectSourcePositionedFanCenterAt
              choice.origin choice.kind choice.index) +
        845 := by
  unfold PeriodicOrthocrossing.translatePolyline at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨localPoint, localPointMember, rfl⟩
  have localBound :=
    retainedDirectSourceFanShiftedTailAt_transverse_band
      choice.kind choice.index slot localPoint localPointMember
  unfold retainedDirectSourcePositionedFanCenterAt
  simp only [Cell.linearValue_add]
  constructor <;> omega

end PeriodicEightOccurrenceSplit
end LeanTrominoes
