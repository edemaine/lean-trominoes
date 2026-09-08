/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingPointCandidateSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineCrossingSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierOwnershipShiftCrossingQuotientSemantics
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATMacrocellCoordinates

/-! # Affine canonical crossing coordinates without a division machine -/

noncomputable section
namespace LeanTrominoes.PeriodicOrthocrossing.CarrierCanonicalCrossingCoordinates
open Computability Turing RouteDescriptorPairAffine
open CarrierCrossingPointField
open RouteDescriptorOccurrenceSlotCrossing
open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags

/-- A canonical crossing macrocell plus a fixed local offset at each side.
Zero offsets give origins; side-local positions give boundary coordinates. -/
def nodePoint (offset : CrossingSide → Cell) (period : Nat) : CarrierNode → Cell
  | .terminal _ => (0, 0)
  | .boundary boundary => Cell.add
      (Cell.scale planarMacroScale
        (boundary.crossing.point.1 % (period : Int), boundary.crossing.point.2 % (period : Int)))
      (offset boundary.side)

def nodeValue (offset : CrossingSide → Cell) (field : Field) (period : Nat) (node : CarrierNode) : Nat :=
  pointValue field (nodePoint offset period node)

def expression (offset : CrossingSide → Cell) (field : Field)
    (occurrences : Occurrence × Occurrence) (side : CrossingSide) : Expression :=
  (((occurrencePairCrossingPointAtShift occurrences (0, 0)).axisExpression (horizontal field)).scale
    planarMacroScale).addConstant (if horizontal field then (offset side).1 else (offset side).2)

/-- Retention translations all use the same unshifted, already canonical point. -/
def shiftBlock (offset : CrossingSide → Cell) (field : Field)
    (occurrences : Occurrence × Occurrence) (_shift : Cell) : List Expression :=
  [expression offset field occurrences .left, expression offset field occurrences .right,
    expression offset field occurrences .top, expression offset field occurrences .bottom]

def occurrenceBlock (offset : CrossingSide → Cell) (field : Field)
    (occurrences : Occurrence × Occurrence) : List Expression :=
  carrierCrossingRetentionShifts.flatMap (shiftBlock offset field occurrences)

def expressions (offset : CrossingSide → Cell) (field : Field) : List Expression :=
  (crossingSlots.map fun slot => occurrenceBlock offset field slot.occurrences).flatten

def fields (offset : CrossingSide → Cell) (field : Field)
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) : List Nat :=
  normalizedFields (keepPositive field) (expressions offset field) (descriptorTokens tokens)

noncomputable def fieldsComputableInPolyTime (offset : CrossingSide → Cell) (field : Field) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields (fields offset field) := by
  let compiled := TM2CompositionMachine.computableInPolyTime
    descriptorTokensComputableInPolyTime
    (normalizedFieldsComputableInPolyTime (keepPositive field) (expressions offset field))
  unfold fields
  exact compiled

/-- On an active slot, wrapping any retained translate recovers the unshifted point. -/
theorem nodePoint_periodTranslate (offset : CrossingSide → Cell) (period : Nat)
    (record : CrossingRecord) (shift : Cell) (side : CrossingSide)
    (bounds : 0 ≤ record.point.1 ∧ record.point.1 < period ∧
      0 ≤ record.point.2 ∧ record.point.2 < period) :
    nodePoint offset period (.boundary ⟨crossingRecordPeriodTranslateAtPeriod period record shift, side⟩) =
      Cell.add (Cell.scale planarMacroScale record.point) (offset side) := by
  unfold nodePoint crossingRecordPeriodTranslateAtPeriod
  simp only [Cell.add, Cell.scale, Int.add_mul_emod_self_left]
  rw [Int.emod_eq_of_lt bounds.1 bounds.2.1, Int.emod_eq_of_lt bounds.2.2.1 bounds.2.2.2]

theorem expression_eq_nodeValue (offset : CrossingSide → Cell) (field : Field)
    (occurrences : Occurrence × Occurrence) (shift : Cell) (side : CrossingSide)
    (pair : RouteDescriptor × RouteDescriptor)
    (bounds :
      let record := occurrencePairCrossingRecordAtPeriod pair.1.gridSize
        (occurrences.1.evalPair .first pair, occurrences.2.evalPair .second pair)
      0 ≤ record.point.1 ∧ record.point.1 < pair.1.gridSize ∧
        0 ≤ record.point.2 ∧ record.point.2 < pair.1.gridSize) :
    normalizedExpressionField (keepPositive field) (expression offset field occurrences side) pair =
      nodeValue offset field pair.1.gridSize
        (.boundary ⟨crossingRecordPeriodTranslateAtPeriod pair.1.gridSize
          (occurrencePairCrossingRecordAtPeriod pair.1.gridSize
            (occurrences.1.evalPair .first pair, occurrences.2.evalPair .second pair)) shift, side⟩) := by
  unfold nodeValue
  rw [nodePoint_periodTranslate offset _ _ _ _ bounds]
  have pointEq := occurrencePairCrossingPointAtShift_evalPair occurrences (0, 0) pair
  simp only [crossingRecordPeriodTranslateAtPeriod, Cell.add, Cell.scale,
    mul_zero, add_zero] at pointEq
  have horizontalEq := congrArg Prod.fst pointEq
  have verticalEq := congrArg Prod.snd pointEq
  change (occurrencePairCrossingPointAtShift occurrences (0, 0)).horizontal.evalPair pair = _ at horizontalEq
  change (occurrencePairCrossingPointAtShift occurrences (0, 0)).vertical.evalPair pair = _ at verticalEq
  cases field <;>
    simp [normalizedExpressionField, expression, horizontal, keepPositive,
      Point.axisExpression, Expression.evalPair_addConstant, Expression.evalPair_scale,
      horizontalEq, verticalEq, pointValue, Cell.add, Cell.scale]

@[simp] theorem fields_descriptorSlotPairTokens (offset : CrossingSide → Cell)
    (field : Field) (pair : TaggedDescriptor × TaggedDescriptor) :
    fields offset field (descriptorSlotPairTokens pair) =
      (expressions offset field).map fun expression =>
        normalizedExpressionField (keepPositive field) expression (pair.1.1, pair.2.1) := by
  unfold fields
  rw [descriptorTokens_descriptorSlotPairTokens]
  have evalEq : ∀ expression : Expression,
      expression.eval (RouteDescriptorPairFieldTags.tokenFieldValue
        (RouteDescriptorPairFieldTags.descriptorPairTokens (pair.1.1, pair.2.1))) =
      expression.evalPair (pair.1.1, pair.2.1) := by
    intro expression
    simpa [Expression.evalTokens] using expression.evalTokens_descriptorPairTokens (pair.1.1, pair.2.1)
  cases field <;> simp [normalizedExpressionField, keepPositive, evalEq]

end LeanTrominoes.PeriodicOrthocrossing.CarrierCanonicalCrossingCoordinates
end
