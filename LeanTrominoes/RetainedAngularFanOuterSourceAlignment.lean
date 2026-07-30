import LeanTrominoes.RetainedAngularFanOuterCorridor

/-!
# Aligning an outer fan corridor with its source terminal segment

The checkpoint tube containing an outer radial route is not an arbitrary
unbounded corridor.  Its checkpoints run inward along the classified source
terminal segment, from the refined source gate toward the variable center.
This file rewrites the gate-based corridor in that source-centered form.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

/-- A point lies in a coordinate-radius tube around the integral
checkpoints of the refined source terminal segment, indexed outward from the
variable center. -/
def InCoordinateSourceTerminalTube
    (radius : Nat)
    (center : Cell)
    (terminal : RetainedTerminalData)
    (point : Cell) : Prop :=
  ∃ index : Nat,
    index ≤
      retainedTerminalFanTotalRefinement * terminal.2 ∧
    WithinCoordinateRadius radius
      (Cell.add center
        (Cell.scale index terminal.1.primitive))
      point

instance (radius : Nat) (center : Cell)
    (terminal : RetainedTerminalData) (point : Cell) :
    Decidable
      (InCoordinateSourceTerminalTube
        radius center terminal point) := by
  unfold InCoordinateSourceTerminalTube
  infer_instance

/-- Every inward checkpoint used by the outer radial route is the same
point as a source-terminal checkpoint indexed outward from the variable
center. -/
theorem retainedTerminalFanOuterInwardCheckpoint_eq_sourceTerminalCheckpoint
    (center : Cell)
    (terminal : RetainedTerminalData)
    (lane : RetainedTerminalSlot)
    (index : Nat)
    (indexBound :
      index ≤
        (retainedTerminalFanOuterInwardRay terminal).length) :
    Cell.add
        (retainedAngularFanOuterDemand
          center terminal lane).gate
        (Cell.scale index
          (retainedTerminalFanOuterInwardRay
            terminal).primitive) =
      Cell.add center
        (Cell.scale
          ((retainedTerminalFanTotalRefinement *
            terminal.2 - index : Nat) : Int)
          terminal.1.primitive) := by
  rcases terminal with ⟨direction, length⟩
  cases direction with
  | compass port =>
      cases port <;>
        apply Prod.ext <;>
        simp [
          retainedAngularFanOuterDemand,
          retainedTerminalSplicePoint,
          scaleRetainedTerminalData,
          retainedTerminalFanOuterInwardRay,
          retainedTerminalFanOuterRadialLength,
          retainedTerminalFanTotalRefinement,
          PeriodicEightOccurrenceSplitPositioned.refinementScale,
          retainedTerminalFanRoutingRefinement,
          retainedTerminalInterfaceMultiplier,
          RetainedTerminalDirection.primitive,
          RetainedRay.primitive, RetainedRay.length,
          oppositePort, OccurrenceSplitRing.Port.unitVector,
          Cell.add, Cell.scale] at indexBound ⊢ <;>
        omega
  | routedClause arm =>
      cases arm <;>
        apply Prod.ext <;>
        simp [
          retainedAngularFanOuterDemand,
          retainedTerminalSplicePoint,
          scaleRetainedTerminalData,
          retainedTerminalFanOuterInwardRay,
          retainedTerminalFanOuterRadialLength,
          retainedTerminalFanTotalRefinement,
          PeriodicEightOccurrenceSplitPositioned.refinementScale,
          retainedTerminalFanRoutingRefinement,
          retainedTerminalInterfaceMultiplier,
          RetainedTerminalDirection.primitive,
          RetainedRay.primitive, RetainedRay.length,
          routedClauseRayPrimitive,
          Cell.add, Cell.sub, Cell.scale] at indexBound ⊢ <;>
        omega

/-- The gate-based checkpoint tube of an outer radial route is contained in
the source-terminal tube around the same classified segment. -/
theorem inCoordinateCheckpointTube_outerInward_to_sourceTerminal
    (radius : Nat)
    (center : Cell)
    (terminal : RetainedTerminalData)
    (lane : RetainedTerminalSlot)
    {point : Cell}
    (bounded :
      InCoordinateCheckpointTube radius
        (retainedAngularFanOuterDemand
          center terminal lane).gate
        (retainedTerminalFanOuterInwardRay terminal).primitive
        (retainedTerminalFanOuterInwardRay terminal).length
        point) :
    InCoordinateSourceTerminalTube
      radius center terminal point := by
  rcases bounded with
    ⟨index, indexBound, pointBound⟩
  refine
    ⟨retainedTerminalFanTotalRefinement *
        terminal.2 - index,
      Nat.sub_le _ _, ?_⟩
  rw [
    ←
      retainedTerminalFanOuterInwardCheckpoint_eq_sourceTerminalCheckpoint
        center terminal lane index indexBound]
  exact pointBound

/-- Every point of the complete outer-fan route lies either near the
refined source terminal segment or in the fixed local square around its
variable center. -/
theorem retainedTerminalFanOuterCompleteRoute_point_in_source_corridor
    (center : Cell)
    (terminal : RetainedTerminalData)
    (lane : RetainedTerminalSlot)
    {point : Cell}
    (pointMember :
      point ∈
        retainedTerminalFanOuterCompleteRoute
          center terminal lane) :
    InCoordinateSourceTerminalTube 65
        center terminal point ∨
      WithinCoordinateRadius 288 center point := by
  rcases
      retainedTerminalFanOuterCompleteRoute_point_in_corridor
        center terminal lane pointMember with
    radial | localBound
  · exact Or.inl
      (inCoordinateCheckpointTube_outerInward_to_sourceTerminal
        65 center terminal lane radial)
  · exact Or.inr localBound

end PeriodicEightOccurrenceSplit
end LeanTrominoes
