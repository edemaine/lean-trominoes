/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanSourceScaledDrawing
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingPointFieldData

/-! # Exact coordinate formula for source-scaled fixed-eight copies -/

namespace LeanTrominoes.PeriodicOrthocrossing
open PeriodicEightOccurrenceSplit PeriodicThreeSATThree

/-- Local ring displacement after the fixed routing refinement. -/
def retainedSplitRingOffset (index : Nat) : Cell :=
  Cell.scale 8 (Cell.sub
    (OccurrenceSplitRing.ringVariablePosition (ringVertexOfIndex index)) (12, 12))

/-- The fixed-eight placement scales each canonical source origin by 1152
and adds the finite ring displacement. -/
theorem retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement_position_eq
    {Variable : Type} [DecidableEq Variable] (source : PeriodicCNF Variable)
    (copy : ThreeOccurrenceVariable (WrappedPeriodicPlanarSATVariable Variable)) :
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source).position copy =
      Cell.add (Cell.scale 1152
        ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source).position copy.1))
        (retainedSplitRingOffset copy.2.1) := by
  apply Prod.ext <;>
    simp [retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement,
      retainedAngularFanSourceScaledRefinedPlacement, retainedAngularFanRefinedPlacement,
      PeriodicVariablePlacement.scale, PeriodicEightOccurrenceSplitPositioned.placement,
      PeriodicEightOccurrenceSplitPositioned.occurrenceVariablePosition,
      PeriodicEightOccurrenceSplitPositioned.macroOrigin,
      PeriodicEightOccurrenceSplitPositioned.refinementScale,
      retainedAngularFanSourceClearanceFactor, retainedTerminalFanRoutingRefinement,
      retainedSplitRingOffset, Cell.add, Cell.sub, Cell.scale] <;> ring

/-- Select a coordinate using the common axis/sign interface. -/
def coordinateFieldOfBools (horizontal keepPositive : Bool) : CarrierCrossingPointField.Field :=
  if horizontal then
    if keepPositive then .horizontalPositive else .horizontalNegative
  else if keepPositive then .verticalPositive else .verticalNegative

@[simp] theorem coordinateFieldOfBools_horizontal (horizontal keepPositive : Bool) :
    CarrierCrossingPointField.horizontal (coordinateFieldOfBools horizontal keepPositive) = horizontal := by
  cases horizontal <;> cases keepPositive <;> rfl

@[simp] theorem coordinateFieldOfBools_keepPositive (horizontal keepPositive : Bool) :
    CarrierCrossingPointField.keepPositive (coordinateFieldOfBools horizontal keepPositive) = keepPositive := by
  cases horizontal <;> cases keepPositive <;> rfl

end LeanTrominoes.PeriodicOrthocrossing
