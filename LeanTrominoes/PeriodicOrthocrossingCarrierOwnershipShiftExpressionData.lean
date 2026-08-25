/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineCandidateExpressionData
import LeanTrominoes.PeriodicOrthocrossingCarrierOwnershipShiftFieldData

/-! # Constant affine expressions for carrier ownership shifts -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open CarrierOwnershipShiftField

def ownershipShiftExpression (field : Field) (shift : Cell) : Expression :=
  let coordinate := if horizontal field then shift.1 else shift.2
  ⟨coordinate, []⟩

def Segment.terminalOwnershipShiftExpressionBlock
    (field : Field) (_segment : Segment) : List Expression :=
  neighborTranslations.flatMap fun translate =>
    List.replicate 2 (ownershipShiftExpression field translate)

def Segment.terminalOwnershipShiftExpressionBlocks
    (field : Field) (segment : Segment) : List (List Expression) :=
  let block := segment.terminalOwnershipShiftExpressionBlock field
  [block, block]

def RouteShape.terminalOwnershipShiftExpressionBlocks
    (field : Field) (shape : RouteShape) : List (List Expression) :=
  (shape.segments .first).flatMap fun segment =>
    segment.terminalOwnershipShiftExpressionBlocks field

def terminalOwnershipShiftExpressionBlocks (field : Field) :
    List (List Expression) :=
  allRouteShapes.flatMap fun shape =>
    shape.terminalOwnershipShiftExpressionBlocks field

def terminalOwnershipShiftExpressions (field : Field) : List Expression :=
  (terminalOwnershipShiftExpressionBlocks field).flatten

def occurrencePairCrossingOwnershipShiftExpressionShiftBlock
    (field : Field) (_occurrences : Occurrence × Occurrence)
    (shift : Cell) : List Expression :=
  List.replicate 4 (ownershipShiftExpression field shift)

def occurrencePairCrossingOwnershipShiftExpressionBlock
    (field : Field) (occurrences : Occurrence × Occurrence) :
    List Expression :=
  carrierCrossingRetentionShifts.flatMap
    (occurrencePairCrossingOwnershipShiftExpressionShiftBlock
      field occurrences)

end RouteDescriptorPairAffine

namespace RouteDescriptorOccurrenceSlotCrossing

open CarrierOwnershipShiftField

def crossingOwnershipShiftExpressionBlocks (field : Field) :
    List (List RouteDescriptorPairAffine.Expression) :=
  crossingSlots.map fun slot =>
    RouteDescriptorPairAffine.occurrencePairCrossingOwnershipShiftExpressionBlock
      field slot.occurrences

def crossingOwnershipShiftExpressions (field : Field) :
    List RouteDescriptorPairAffine.Expression :=
  (crossingOwnershipShiftExpressionBlocks field).flatten

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
