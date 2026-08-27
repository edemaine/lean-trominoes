/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionDirections
import LeanTrominoes.RetainedAngularFanDirectSourceNormalizedTailQuery

/-! # Complete normalized direct-source tail lookup -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open Gadget

/-- Total finite lookup of the complete normalized direction word. -/
def retainedDirectSourceNormalizedDirectionsOfTailQuery
    (query : RetainedDirectSourceNormalizedTailQuery) :
    List AxisDirection :=
  if indexLt :
      query.literalIndex.val <
        (retainedDirectSourcePrefixChoices query.kind).length then
    unitSubdivisionDirections
      (AxisDirection.normalizeOrthogonalPolyline
        ((retainedDirectSourceZeroChoice query.kind
          ⟨query.literalIndex.val, indexLt⟩).completeFigure7Route
            query.slot))
  else
    []

/-- The dynamic Figure Nine source tail deletes the clause-side direction
from the complete normalized direct-atlas word. -/
def retainedDirectSourceNormalizedTailOfQuery
    (query : RetainedDirectSourceNormalizedTailQuery) :
    List AxisDirection :=
  (retainedDirectSourceNormalizedDirectionsOfTailQuery query).tail

end PeriodicEightOccurrenceSplit
end LeanTrominoes
