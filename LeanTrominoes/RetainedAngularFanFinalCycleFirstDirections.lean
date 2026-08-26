/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanCycleFirstDirections
import LeanTrominoes.RetainedAngularFanFinalCycleSeparation
import LeanTrominoes.RetainedAngularFanFinalNormalizedRouteFamily
import LeanTrominoes.PeriodicCNFPlanarFixedEightOneInThreeVariableRouteOrder

/-! # Clause-side directions of final normalized cycle routes -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

/-- Normalizing a genuine appended implication-cycle route preserves the
first direction of its unscaled positioned Figure 7 route. -/
theorem
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_cycle_firstDirection
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
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    let source :=
      (finalCoordinatedSource formula).scale
        retainedAngularFanSourceClearanceFactor
    let placement :=
      (finalCoordinatedPlacement formula).scale
        retainedAngularFanSourceClearanceFactor
    let routes :=
      PositionedPeriodicCNF.scaleIncidenceRoutes
        retainedAngularFanSourceClearanceFactor
        (finalCoordinatedSourceRoutes formula)
    let occurrencePorts :=
      occurrencePortsOfAngularOrder
        source.erase
        (angularOccurrenceOrder source.erase routes)
    AxisDirection.polylineFirstDirection
        (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
          formula
          ((occurrenceClauses source occurrencePorts).length + cycleIndex)
          literalIndex) =
      AxisDirection.polylineFirstDirection
        (allCycleRoutes source placement cycleIndex literalIndex) := by
  dsimp only
  let source :=
    (finalCoordinatedSource formula).scale
      retainedAngularFanSourceClearanceFactor
  let placement :=
    (finalCoordinatedPlacement formula).scale
      retainedAngularFanSourceClearanceFactor
  let route :=
    allCycleRoutes source placement cycleIndex literalIndex
  have routeLength : 2 ≤ route.length :=
    allCycleRoutes_length_ge_two
      source placement clauseMember literalMember
  have routeOrthogonal : OrthogonalPolyline route :=
    allCycleRoutes_orthogonal
      source placement clauseMember literalMember
  have scaledSimple :
      LocalIncidenceDrawing.RouteIsSimple
        (scalePolyline retainedTerminalFanRoutingRefinement route) := by
    simpa only [source, placement, route] using
      retainedFinalSourceScaledAllCycleRoute_isSimple
        formula clauseMember literalMember
  change
    AxisDirection.polylineFirstDirection
        (AxisDirection.normalizeOrthogonalPolyline
          (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
            formula _ literalIndex)) = _
  rw [retainedFinalCoordinatedCycleRoute_eq_scaledAllCycleRoute
    formula cycleIndex literalIndex]
  calc
    _ = AxisDirection.polylineFirstDirection
          (scalePolyline retainedTerminalFanRoutingRefinement route) :=
      AxisDirection.polylineFirstDirection_normalizeOrthogonalPolyline_of_simple
        (by simpa [scalePolyline] using routeLength)
        (routeOrthogonal.scalePolyline (by
          simp [retainedTerminalFanRoutingRefinement]))
        scaledSimple
    _ = AxisDirection.polylineFirstDirection route :=
      AxisDirection.polylineFirstDirection_scalePolyline
        retainedTerminalFanRoutingRefinement
        (by simp [retainedTerminalFanRoutingRefinement]) route

/-- At the explicit block/local index of one source atom, the final
normalized route exposes exactly the first direction of the corresponding
local Figure 7 incidence. -/
theorem
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_cycleBlockStart_firstDirection
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (atom : WrappedPeriodicPlanarSATVariable Variable)
    (atomMember :
      atom ∈
        sourceVariables
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor).erase)
    (localClauseIndex literalIndex : Nat)
    (localIndex :
      localClauseIndex <
        (PeriodicEightOccurrenceSplit.cycleClausesFor atom).length)
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    (clauseMember :
      (clause,
        cycleBlockStart
            (sourceVariables
              ((finalCoordinatedSource formula).scale
                retainedAngularFanSourceClearanceFactor).erase)
            atom +
          localClauseIndex) ∈
        (allCycleClauses
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)).zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    let source :=
      (finalCoordinatedSource formula).scale
        retainedAngularFanSourceClearanceFactor
    let routes :=
      PositionedPeriodicCNF.scaleIncidenceRoutes
        retainedAngularFanSourceClearanceFactor
        (finalCoordinatedSourceRoutes formula)
    let occurrencePorts :=
      occurrencePortsOfAngularOrder
        source.erase
        (angularOccurrenceOrder source.erase routes)
    AxisDirection.polylineFirstDirection
        (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
          formula
          ((occurrenceClauses source occurrencePorts).length +
            (cycleBlockStart (sourceVariables source.erase) atom +
              localClauseIndex))
          literalIndex) =
      AxisDirection.polylineFirstDirection
        (OccurrenceSplitRing.cycleRoutes
          localClauseIndex literalIndex) := by
  dsimp only
  let source :=
    (finalCoordinatedSource formula).scale
      retainedAngularFanSourceClearanceFactor
  let placement :=
    (finalCoordinatedPlacement formula).scale
      retainedAngularFanSourceClearanceFactor
  calc
    _ = AxisDirection.polylineFirstDirection
          (allCycleRoutes source placement
            (cycleBlockStart (sourceVariables source.erase) atom +
              localClauseIndex)
            literalIndex) :=
      retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_cycle_firstDirection
        formula clauseMember literalMember
    _ = AxisDirection.polylineFirstDirection
          (OccurrenceSplitRing.cycleRoutes
            localClauseIndex literalIndex) :=
      allCycleRoutes_cycleBlockStart_firstDirection
        source placement atom atomMember
        localClauseIndex literalIndex localIndex

end PeriodicOrthocrossing
end LeanTrominoes
