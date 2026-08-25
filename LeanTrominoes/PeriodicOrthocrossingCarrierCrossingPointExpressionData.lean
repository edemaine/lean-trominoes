/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingPointFieldData
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineCandidateExpressionData

/-! # Affine expressions for crossing-point rank fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open CarrierCrossingPointField

/-- The same crossing-point coordinate belongs to all four boundary nodes of
one retained crossing. -/
def occurrencePairCrossingPointExpressionShiftBlock
    (field : Field) (occurrences : Occurrence × Occurrence)
    (shift : Cell) : List Expression :=
  let expression :=
    (occurrencePairCrossingPointAtShift occurrences shift).axisExpression
      (horizontal field)
  [expression, expression, expression, expression]

def occurrencePairCrossingPointExpressionBlock
    (field : Field) (occurrences : Occurrence × Occurrence) :
    List Expression :=
  carrierCrossingRetentionShifts.flatMap
    (occurrencePairCrossingPointExpressionShiftBlock field occurrences)

end RouteDescriptorPairAffine

namespace RouteDescriptorOccurrenceSlotCrossing

open CarrierCrossingPointField

def crossingPointExpressionBlocks (field : Field) :
    List (List RouteDescriptorPairAffine.Expression) :=
  crossingSlots.map fun slot =>
    RouteDescriptorPairAffine.occurrencePairCrossingPointExpressionBlock
      field slot.occurrences

def crossingPointExpressions (field : Field) :
    List RouteDescriptorPairAffine.Expression :=
  (crossingPointExpressionBlocks field).flatten

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
