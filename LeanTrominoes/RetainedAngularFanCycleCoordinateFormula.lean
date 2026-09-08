/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCycleRingLiteralSemantics
import LeanTrominoes.RetainedAngularFanSplitCoordinateFormula
import LeanTrominoes.SignedUnaryCoordinateRefinementCompiler

/-! # Ring-slot decoding and exact implication-cycle copy coordinates -/

namespace LeanTrominoes.PeriodicCNFStripReduction
open PeriodicOrthocrossing PeriodicEightOccurrenceSplit OccurrenceSplitRing

/-- Decode the compiler's eight angular port slots and separator slot. -/
def directFinalCycleRingVertexOfSlot (slot : DirectFinalCycleRingVertexSlot) : RingVertex :=
  if slot.val = 8 then .separator else .port (angularPortOfIndex slot.val)

@[simp] theorem directFinalCycleRingVertexOfSlot_slot (vertex : RingVertex) :
    directFinalCycleRingVertexOfSlot (directFinalCycleRingVertexSlot vertex) = vertex := by
  cases vertex with
  | separator => rfl
  | port port => cases port <;> rfl

@[simp] theorem directFinalCycleRingVertexSlot_ofSlot (slot : DirectFinalCycleRingVertexSlot) :
    directFinalCycleRingVertexSlot (directFinalCycleRingVertexOfSlot slot) = slot := by
  fin_cases slot <;> rfl

/-- An active inherited scope decodes to its actual parent-clause literal. -/
theorem directFinalCycleRingVertexOfSlot_literal_inherited
    (clause : PositionedPeriodicClause RingVertex)
    (slot : PeriodicCNF.ClauseProfilePolarityRouteOperation.SourceLiteralSlot)
    (active : PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader.sourceSlotNat slot < clause.literals.length) :
    directFinalCycleRingVertexOfSlot (directFinalCycleLiteralSlot clause (.inherited slot)) =
      (clause.literals[PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader.sourceSlotNat slot]'active).atom := by
  simp only [directFinalCycleLiteralSlot, List.getElem?_eq_getElem active,
    Option.map_some, Option.getD_some, directFinalCycleRingVertexOfSlot_slot]

/-- The local ring displacement applies to compass ports and the separator. -/
def retainedSplitRingVertexOffset (vertex : RingVertex) : Cell :=
  Cell.scale 8 (Cell.sub (ringVariablePosition vertex) (12, 12))

/-- Actual ring-copy coordinates with owner and finite vertex explicit. -/
theorem retainedSplitRingCopy_coordinate {Atom : Type} [DecidableEq Atom]
    (source : PeriodicCNF Atom) (horizontal positive : Bool)
    (atom : WrappedPeriodicPlanarSATVariable Atom) (vertex : RingVertex) :
    CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal positive)
        ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source).position
          (ringCopy atom vertex)) =
      SignedUnaryCoordinateRefinement.field positive
        (1152 * (let position := (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source).position atom
          if horizontal then position.1 else position.2) +
        (let offset := retainedSplitRingVertexOffset vertex
          if horizontal then offset.1 else offset.2)) := by
  rw [retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement_position_eq]
  have owner : (ringCopy atom vertex).1 = atom := by cases vertex <;> rfl
  have offset : retainedSplitRingOffset (ringCopy atom vertex).2.1 =
      retainedSplitRingVertexOffset vertex := by
    cases vertex with
    | separator => rfl
    | port port => cases port <;> rfl
  rw [owner, offset]
  simp only [CarrierCrossingPointField.pointValue, coordinateFieldOfBools_horizontal,
    coordinateFieldOfBools_keepPositive, SignedUnaryCoordinateRefinement.field]
  cases horizontal <;> rfl

end LeanTrominoes.PeriodicCNFStripReduction
