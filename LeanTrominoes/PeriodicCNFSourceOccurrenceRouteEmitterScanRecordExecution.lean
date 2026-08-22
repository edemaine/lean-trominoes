/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterScanRecordNilExecution
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterScanRecordConsExecution

/-! # Uniform offset-record execution inside occurrence scanning -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF.SourceOccurrenceRouteEmitterMachine

noncomputable def scanRecord_evalsInTime (base : TapeData)
    (state : ScanState) (value : Bool)
    (tokens : List SourceOccurrenceRouteTokens.Token) :
    let next := state.readOffset base.clauseCount.length
      base.literalCount.length value
    EvalsToInTime machine.step
      (beginRecordCfg next.cursor (scanData base state tokens))
      (some (scanOccurrencesCfg next.cursor (scanData base next tokens)))
      (recordTime (scanData base state tokens)
        (state.targets.head?.getD 0)) := by
  simp only
  cases targetsEq : state.targets with
  | nil =>
      simpa only [List.head?_nil, Option.getD_none] using
        scanRecord_nil_evalsInTime base state value tokens targetsEq
  | cons target remaining =>
      simpa only [List.head?_cons, Option.getD_some] using
        scanRecord_cons_evalsInTime base state value tokens target
          remaining targetsEq

end PeriodicCNF.SourceOccurrenceRouteEmitterMachine
end LeanTrominoes
