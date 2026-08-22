/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterScanData

/-! # Exact occurrence-scan execution time -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine

open SourceOccurrenceRouteTokens

def scanTime (base : TapeData) :
    ScanState → List Token → Nat
  | _, [] => 1
  | state, .clause _ :: tokens =>
      scanTime base state.readClause tokens + 1
  | state, .literal index :: tokens =>
      scanTime base (state.readLiteral index) tokens + 1
  | state, .offsetNext value :: tokens =>
      let next := state.readOffset base.clauseCount.length
        base.literalCount.length value
      scanTime base next tokens +
        (recordTime (scanData base state tokens)
          (state.targets.head?.getD 0) + 1)
  | state, .literalEnd :: tokens =>
      scanTime base state tokens + 1

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine
