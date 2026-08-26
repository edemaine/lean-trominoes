/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCopiedSourceDirectionQuery
import LeanTrominoes.FiniteBlockTransducer

/-! # Compiling mixed final copied-source direction queries -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open Computability Turing

local instance retainedFinalCopiedSourceDirectionInhabited :
    Inhabited AxisDirection :=
  ⟨.invalid⟩

/-- Mixed direct/fallback direction queries are evaluated by a fixed finite
one-pass transducer. -/
noncomputable def retainedFinalCopiedSourceDirectionsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List RetainedFinalCopiedSourceDirectionQuery)
      (List AxisDirection)
      RetainedFinalCopiedSourceDirectionQuery AxisDirection
      id id retainedFinalCopiedSourceDirections :=
  FiniteBlockTransducer.computableInPolyTime fun query =>
    [retainedFinalCopiedSourceDirectionOfQuery query]

end PeriodicEightOccurrenceSplit
end LeanTrominoes

end
