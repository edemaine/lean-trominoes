/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizationOffsetFieldData
import LeanTrominoes.PeriodicOrthocrossingCarrierOwnershipShiftExpressionData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairRoutePointGaugeData

/-! # Constant affine expressions for carrier normalization offsets -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open CarrierNormalizationOffsetField

def normalizationOffsetExpression
    (field : Field) (translate gauge : Cell) : Expression :=
  let offset := Cell.add translate gauge
  let coordinate := if horizontal field then offset.1 else offset.2
  ⟨coordinate, []⟩

def GaugedSegment.terminalNormalizationOffsetExpressionBlock
    (field : Field) (gauged : GaugedSegment) : List Expression :=
  neighborTranslations.flatMap fun translate =>
    [normalizationOffsetExpression field translate gauged.startGauge,
      normalizationOffsetExpression field translate gauged.finishGauge]

def GaugedSegment.terminalNormalizationOffsetExpressionBlocks
    (field : Field) (gauged : GaugedSegment) : List (List Expression) :=
  let block := gauged.terminalNormalizationOffsetExpressionBlock field
  [block, block]

def RouteShape.terminalNormalizationOffsetExpressionBlocks
    (field : Field) (shape : RouteShape) : List (List Expression) :=
  (shape.gaugedSegments .first).flatMap fun gauged =>
    gauged.terminalNormalizationOffsetExpressionBlocks field

def terminalNormalizationOffsetExpressionBlocks (field : Field) :
    List (List Expression) :=
  allRouteShapes.flatMap fun shape =>
    shape.terminalNormalizationOffsetExpressionBlocks field

def terminalNormalizationOffsetExpressions (field : Field) :
    List Expression :=
  (terminalNormalizationOffsetExpressionBlocks field).flatten

def occurrencePairCrossingNormalizationOffsetExpressionShiftBlock
    (field : Field) (_occurrences : Occurrence × Occurrence)
    (shift : Cell) : List Expression :=
  List.replicate 4
    (normalizationOffsetExpression field shift (0, 0))

def occurrencePairCrossingNormalizationOffsetExpressionBlock
    (field : Field) (occurrences : Occurrence × Occurrence) :
    List Expression :=
  carrierCrossingRetentionShifts.flatMap
    (occurrencePairCrossingNormalizationOffsetExpressionShiftBlock
      field occurrences)

end RouteDescriptorPairAffine

namespace RouteDescriptorOccurrenceSlotCrossing

open CarrierNormalizationOffsetField

def crossingNormalizationOffsetExpressionBlocks (field : Field) :
    List (List RouteDescriptorPairAffine.Expression) :=
  crossingSlots.map fun slot =>
    RouteDescriptorPairAffine.occurrencePairCrossingNormalizationOffsetExpressionBlock
      field slot.occurrences

def crossingNormalizationOffsetExpressions (field : Field) :
    List RouteDescriptorPairAffine.Expression :=
  (crossingNormalizationOffsetExpressionBlocks field).flatten

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
