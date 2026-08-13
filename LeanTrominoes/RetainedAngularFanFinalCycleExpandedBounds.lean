/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCycleBounds
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedVariablePositions

/-!
# Expanded-period bounds for final implication-cycle routes

Every implication-cycle route is contained in a fixed radius-48 square about
the fully refined position of the source atom that owns its cycle block.
Canonical gauging puts that atom strictly inside the unrefined fundamental
square, so the large fixed-eight refinement leaves ample boundary margin.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

/-- Every point of a genuine final implication-cycle route lies in the open
neighboring-period square of the source-scaled fixed-eight placement. -/
theorem retainedFinalSourceScaledAllCycleRoute_point_inExpanded
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {cycleIndex : Nat}
    (clauseMember :
      (clause, cycleIndex) ∈
        (allCycleClauses
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)).zipIdx)
    (literalIndex : Nat)
    {point : Cell}
    (pointMember :
      point ∈
        scalePolyline retainedTerminalFanRoutingRefinement
          (allCycleRoutes
            ((finalCoordinatedSource formula).scale
              retainedAngularFanSourceClearanceFactor)
            ((finalCoordinatedPlacement formula).scale
              retainedAngularFanSourceClearanceFactor)
            cycleIndex literalIndex)) :
    let refinedPeriod : Int :=
      (retainedTerminalFanTotalRefinement *
        retainedAngularFanSourceClearanceFactor) *
          (finalCoordinatedPlacement formula).period;
    -refinedPeriod < point.1 ∧
      point.1 < 2 * refinedPeriod ∧
      -refinedPeriod < point.2 ∧
      point.2 < 2 * refinedPeriod := by
  rcases
      retainedFinalSourceScaledAllCycleRoute_point_in_centerRectangle
        formula clauseMember literalIndex pointMember with
    ⟨atom, _atomMember, bounded⟩
  rcases centerEq :
      (finalCoordinatedPlacement formula).position atom with
    ⟨centerX, centerY⟩
  rcases point with ⟨pointX, pointY⟩
  have centerInsideRaw :
      0 < ((finalCoordinatedPlacement formula).position atom).1 ∧
        ((finalCoordinatedPlacement formula).position atom).1 <
          (finalCoordinatedPlacement formula).period ∧
        0 < ((finalCoordinatedPlacement formula).position atom).2 ∧
        ((finalCoordinatedPlacement formula).position atom).2 <
          (finalCoordinatedPlacement formula).period := by
    simpa only [finalCoordinatedPlacement] using
      retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_position_inSquare
        formula atom
  have centerInside :
      0 < centerX ∧
        centerX < (finalCoordinatedPlacement formula).period ∧
        0 < centerY ∧
        centerY < (finalCoordinatedPlacement formula).period := by
    simpa only [centerEq] using centerInsideRaw
  simp only [InClosedGridRectangle,
    coordinateRadiusLower, coordinateRadiusUpper,
    Cell.scale, centerEq] at bounded
  dsimp only
  norm_num [retainedTerminalFanTotalRefinement_eq,
    retainedAngularFanSourceClearanceFactor]
    at bounded ⊢
  omega

end PeriodicOrthocrossing
end LeanTrominoes
