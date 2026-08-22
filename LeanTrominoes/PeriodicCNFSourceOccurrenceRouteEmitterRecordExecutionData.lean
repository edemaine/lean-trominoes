/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterRecordCountersExecution

/-! # One-record execution data for source-occurrence route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine

def beginRecordData (data : TapeData) : TapeData :=
  { data with outputReverse := .clauseMarker :: data.outputReverse }

def afterTargetData (data : TapeData) (targetCount : Nat)
    (remainingTargets : List UnarySymbol) : TapeData :=
  { data with
    targets := remainingTargets
    outputReverse :=
      .atomEnd :: List.replicate targetCount .atomUnit ++
        data.outputReverse }

def afterFinishedRecordData (data : TapeData) (targetCount : Nat)
    (remainingTargets : List UnarySymbol) (literalIndex : Fin 3)
    (currentNext anchorNext : Bool) : TapeData :=
  let target := afterTargetData data targetCount remainingTargets
  { target with
    edgeIndex := () :: target.edgeIndex
    outputReverse :=
      (fixedSuffix literalIndex currentNext anchorNext).reverse ++
        target.outputReverse }

def recordSuffixTime (targetCount : Nat) : Nat :=
  1 + (targetCount + 1)

def recordTime (data : TapeData) (targetCount : Nat) : Nat :=
  recordSuffixTime targetCount +
    (recordCountersTime (beginRecordData data) + 1)

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine
