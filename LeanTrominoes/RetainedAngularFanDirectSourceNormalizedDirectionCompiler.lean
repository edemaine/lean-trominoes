/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanDirectSourceNormalizedDirectionQuery
import LeanTrominoes.FiniteBlockTransducer

/-! # Compiling direct-source normalized direction queries -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open Computability Turing

local instance retainedDirectNormalizedDirectionInhabited :
    Inhabited AxisDirection :=
  ⟨.invalid⟩

/-- The slot-sensitive normalized direct-source lookup is a fixed finite
one-pass transduction. -/
noncomputable def retainedDirectSourceNormalizedDirectionsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List RetainedDirectSourceNormalizedDirectionQuery)
      (List AxisDirection)
      RetainedDirectSourceNormalizedDirectionQuery AxisDirection
      id id retainedDirectSourceNormalizedDirections :=
  FiniteBlockTransducer.computableInPolyTime fun query =>
    [retainedDirectSourceNormalizedDirectionOfQuery query]

end PeriodicEightOccurrenceSplit
end LeanTrominoes

end
