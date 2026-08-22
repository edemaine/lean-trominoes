/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterRecordCounterData

/-! # Edge-index field execution for source-occurrence route emission -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF.SourceOccurrenceRouteEmitterMachine

noncomputable def edgeIndexCounter_evalsInTime (cursor : Cursor)
    (data : TapeData) (scratchEq : data.scratch = []) :
    EvalsToInTime machine.step
      (copyCounterCfg .edgeIndex cursor data)
      (some (copyCounterCfg .sourceLiterals cursor
        (afterEdgeIndexCounter data)))
      (counterTime data.edgeIndex) := by
  have run := counter_evalsInTime .edgeIndex cursor data
    data.edgeIndex rfl scratchEq
  simpa only [afterCounterCfg, afterEdgeIndexCounter,
    closeOutputField] using run

end PeriodicCNF.SourceOccurrenceRouteEmitterMachine
end LeanTrominoes
