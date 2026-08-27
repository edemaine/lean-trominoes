/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionDirectionsTail
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionDirectionTranslation
import LeanTrominoes.RetainedAngularFanFinalCycleFirstDirections
import LeanTrominoes.RetainedAngularFanFinalRelativeCycleSeparation

/-! # Complete direction words of final normalized cycle routes -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open Gadget
open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

/-- Normalizing a genuine final implication-cycle route preserves its whole
unit-subdivision direction word, not just its first direction. -/
theorem
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_cycle_directions
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
    unitSubdivisionDirections
        (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
          formula
          ((occurrenceClauses source occurrencePorts).length + cycleIndex)
          literalIndex) =
      unitSubdivisionDirections
        (scalePolyline retainedTerminalFanRoutingRefinement
          (allCycleRoutes source placement cycleIndex literalIndex)) := by
  dsimp only
  let source :=
    (finalCoordinatedSource formula).scale
      retainedAngularFanSourceClearanceFactor
  let placement :=
    (finalCoordinatedPlacement formula).scale
      retainedAngularFanSourceClearanceFactor
  let route := allCycleRoutes source placement cycleIndex literalIndex
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
  change unitSubdivisionDirections
      (AxisDirection.normalizeOrthogonalPolyline
        (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
          formula _ literalIndex)) = _
  rw [retainedFinalCoordinatedCycleRoute_eq_scaledAllCycleRoute
    formula cycleIndex literalIndex]
  have routeNonempty : route ≠ [] := by
    intro empty
    rw [empty] at routeLength
    simp at routeLength
  have scaledNonempty :
      scalePolyline retainedTerminalFanRoutingRefinement route ≠ [] := by
    simpa [scalePolyline] using routeNonempty
  exact unitSubdivisionDirections_normalizeOrthogonalPolyline_of_simple
    (by simpa only [source, placement, route] using scaledNonempty)
    (routeOrthogonal.scalePolyline (by
      simp [retainedTerminalFanRoutingRefinement]))
    scaledSimple

/-- A genuine final implication-cycle route is unit subdivided after public
normalization.  Keeping this consequence next to the complete direction-word
identity avoids importing the global source admissibility package. -/
theorem
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_cycle_unitSteps
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
    let routes :=
      PositionedPeriodicCNF.scaleIncidenceRoutes
        retainedAngularFanSourceClearanceFactor
        (finalCoordinatedSourceRoutes formula)
    let occurrencePorts :=
      occurrencePortsOfAngularOrder
        source.erase
        (angularOccurrenceOrder source.erase routes)
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
      formula
      ((occurrenceClauses source occurrencePorts).length + cycleIndex)
      literalIndex).IsChain AxisDirection.IsUnitAxisStep := by
  dsimp only
  let source :=
    (finalCoordinatedSource formula).scale
      retainedAngularFanSourceClearanceFactor
  let placement :=
    (finalCoordinatedPlacement formula).scale
      retainedAngularFanSourceClearanceFactor
  let route := allCycleRoutes source placement cycleIndex literalIndex
  have routeLength : 2 ≤ route.length :=
    allCycleRoutes_length_ge_two
      source placement clauseMember literalMember
  have routeOrthogonal : OrthogonalPolyline route :=
    allCycleRoutes_orthogonal
      source placement clauseMember literalMember
  have routeNonempty : route ≠ [] := by
    intro empty
    rw [empty] at routeLength
    simp at routeLength
  have scaledNonempty :
      scalePolyline retainedTerminalFanRoutingRefinement route ≠ [] := by
    simpa [scalePolyline] using routeNonempty
  change
    (AxisDirection.normalizeOrthogonalPolyline
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula _ literalIndex)).IsChain AxisDirection.IsUnitAxisStep
  rw [retainedFinalCoordinatedCycleRoute_eq_scaledAllCycleRoute
    formula cycleIndex literalIndex]
  exact AxisDirection.normalizeOrthogonalPolyline_unitSteps
    (by simpa only [source, placement, route] using scaledNonempty)
    (routeOrthogonal.scalePolyline (by
      simp [retainedTerminalFanRoutingRefinement]))

/-- At a genuine stable source-variable block, the complete normalized route
word is the fixed local Figure Seven route word after the final scale. -/
theorem
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_cycleBlockStart_directions
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
    unitSubdivisionDirections
        (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
          formula
          ((occurrenceClauses source occurrencePorts).length +
            (cycleBlockStart (sourceVariables source.erase) atom +
              localClauseIndex))
          literalIndex) =
      unitSubdivisionDirections
        (scalePolyline retainedTerminalFanRoutingRefinement
          (OccurrenceSplitRing.cycleRoutes
            localClauseIndex literalIndex)) := by
  dsimp only
  let source :=
    (finalCoordinatedSource formula).scale
      retainedAngularFanSourceClearanceFactor
  let placement :=
    (finalCoordinatedPlacement formula).scale
      retainedAngularFanSourceClearanceFactor
  calc
    _ = unitSubdivisionDirections
          (scalePolyline retainedTerminalFanRoutingRefinement
            (allCycleRoutes source placement
              (cycleBlockStart (sourceVariables source.erase) atom +
                localClauseIndex)
              literalIndex)) :=
      retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_cycle_directions
        formula clauseMember literalMember
    _ = unitSubdivisionDirections
          (scalePolyline retainedTerminalFanRoutingRefinement
            (positionedCycleRoutes placement atom
              localClauseIndex literalIndex)) := by
      rw [allCycleRoutes_cycleBlockStart
        source placement atom atomMember
        localClauseIndex literalIndex localIndex]
    _ = unitSubdivisionDirections
          (scalePolyline retainedTerminalFanRoutingRefinement
            (OccurrenceSplitRing.cycleRoutes
              localClauseIndex literalIndex)) := by
      unfold positionedCycleRoutes OccurrenceSplitRing.translatedCycleDrawing
        PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.translate
        OccurrenceSplitRing.cycleDrawing
      change unitSubdivisionDirections
          (scalePolyline retainedTerminalFanRoutingRefinement
            (translatePolyline (macroOrigin placement atom)
              (OccurrenceSplitRing.cycleRoutes
                localClauseIndex literalIndex))) = _
      rw [scalePolyline_translatePolyline,
        unitSubdivisionDirections_translatePolyline]

/-- Deleting the clause-side point of a normalized cycle route deletes
exactly the first token of its fixed local Figure Seven direction word. -/
theorem
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_cycleBlockStart_tailDirections
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
    unitSubdivisionDirections
        (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
          formula
          ((occurrenceClauses source occurrencePorts).length +
            (cycleBlockStart (sourceVariables source.erase) atom +
              localClauseIndex))
          literalIndex).tail =
      (unitSubdivisionDirections
        (scalePolyline retainedTerminalFanRoutingRefinement
          (OccurrenceSplitRing.cycleRoutes
            localClauseIndex literalIndex))).tail := by
  dsimp only
  let source :=
    (finalCoordinatedSource formula).scale
      retainedAngularFanSourceClearanceFactor
  let route :=
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
      formula
      ((occurrenceClauses source
        (occurrencePortsOfAngularOrder source.erase
          (angularOccurrenceOrder source.erase
            (PositionedPeriodicCNF.scaleIncidenceRoutes
              retainedAngularFanSourceClearanceFactor
              (finalCoordinatedSourceRoutes formula))))).length +
        (cycleBlockStart (sourceVariables source.erase) atom +
          localClauseIndex))
      literalIndex
  have unitSteps : route.IsChain AxisDirection.IsUnitAxisStep := by
    simpa only [source, route] using
      retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_cycle_unitSteps
        formula clauseMember literalMember
  rw [unitSubdivisionDirections_tail_eq_tail_of_unitSteps route unitSteps]
  apply congrArg List.tail
  simpa only [source, route] using
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_cycleBlockStart_directions
      formula atom atomMember localClauseIndex literalIndex localIndex
      clauseMember literalMember

end PeriodicOrthocrossing
end LeanTrominoes
