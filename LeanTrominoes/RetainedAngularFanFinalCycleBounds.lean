import LeanTrominoes.RetainedAngularFanFinalCycleSeparation
import LeanTrominoes.RetainedAngularFanSourceSplicePointSeparation

/-!
# Uniform bounds for the final implication-cycle routes

Every local Figure 7 implication route lies in the inner `12 × 12` square
of its occurrence-splitting macrocell.  After the factor-eight terminal-fan
refinement, this becomes a radius-48 neighborhood of the fully refined
position of the source atom that owns the cycle block.

This module also returns that owning atom and its source-membership
certificate.  Mixed copied-source/cycle separation can therefore distinguish
the route's own endpoint neighborhood from every other source vertex.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

set_option maxHeartbeats 2000000

/-- Every point of a genuine final implication route lies within coordinate
radius 48 of the fully refined position of the source atom owning its cycle
block. -/
theorem retainedFinalSourceScaledAllCycleRoute_point_in_centerRectangle
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
    ∃ atom :
        WrappedPeriodicPlanarSATVariable Variable,
      atom ∈
          sourceVariables
            ((finalCoordinatedSource formula).scale
              retainedAngularFanSourceClearanceFactor).erase ∧
        InClosedGridRectangle
          (coordinateRadiusLower 48
            (Cell.scale
              (retainedTerminalFanTotalRefinement *
                retainedAngularFanSourceClearanceFactor)
              ((finalCoordinatedPlacement formula).position atom)))
          (coordinateRadiusUpper 48
            (Cell.scale
              (retainedTerminalFanTotalRefinement *
                retainedAngularFanSourceClearanceFactor)
              ((finalCoordinatedPlacement formula).position atom)))
          point := by
  let source :=
    (finalCoordinatedSource formula).scale
      retainedAngularFanSourceClearanceFactor
  let placement :=
    (finalCoordinatedPlacement formula).scale
      retainedAngularFanSourceClearanceFactor
  rcases allCycleClauseMetadata_lookup_valid
      source placement clauseMember with
    ⟨metadata, metadataLookup, _clauseEqual,
      _localClauseMember⟩
  have atomMember :=
    allCycleClauseMetadata_lookup_atom_mem
      source placement metadataLookup
  rw [scalePolyline, List.mem_map] at pointMember
  rcases pointMember with
    ⟨localPoint, localPointMember, rfl⟩
  have localPointMember' :
      localPoint ∈
        positionedCycleRoutes placement metadata.atom
          metadata.localClauseIndex literalIndex := by
    change
      localPoint ∈
        allCycleRoutes source placement cycleIndex literalIndex
      at localPointMember
    unfold allCycleRoutes at localPointMember
    rw [metadataLookup] at localPointMember
    exact localPointMember
  have localBound :=
    positionedCycleRoutes_inClosedGridRectangle
      placement metadata.atom metadata.localClauseIndex
      literalIndex localPointMember'
  refine ⟨metadata.atom, atomMember, ?_⟩
  rcases positionEq :
      (finalCoordinatedPlacement formula).position metadata.atom with
    ⟨centerX, centerY⟩
  rcases localPoint with ⟨pointX, pointY⟩
  simp only [placement,
    positionedCycleRouteLower, positionedCycleRouteUpper,
    macroOrigin, PeriodicVariablePlacement.scale,
    coordinateRadiusLower, coordinateRadiusUpper,
    retainedTerminalFanTotalRefinement_eq,
    retainedTerminalFanRoutingRefinement,
    retainedAngularFanSourceClearanceFactor,
    refinementScale, positionEq, InClosedGridRectangle,
    Cell.add, Cell.sub, Cell.scale]
    at localBound ⊢
  omega

end PeriodicOrthocrossing
end LeanTrominoes
