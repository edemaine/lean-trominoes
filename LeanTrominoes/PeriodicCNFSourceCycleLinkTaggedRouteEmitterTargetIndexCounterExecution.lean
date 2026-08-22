/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterRecordCounterData

/-! # Target-record target-index field execution -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

noncomputable def targetIndexCounter_evalsInTime (tag : Tag)
    (data : TapeData) (scratchEq : data.scratch = []) :
    EvalsToInTime machine.step
      (copyCounterCfg .targetTargetIndex tag data)
      (some (finishTargetRecordCfg tag
        (afterTargetTargetIndexCounter data)))
      (counterTime data.linkIndex) := by
  have index := counter_evalsInTime .targetTargetIndex tag data
    data.linkIndex rfl scratchEq
  simpa only [afterCounterCfg,
    afterTargetTargetIndexCounter] using index

end PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
end LeanTrominoes
