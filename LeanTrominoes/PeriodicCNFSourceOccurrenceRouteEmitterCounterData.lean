/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterCounterTapeUpdates

/-! # Uniform counter data for source-occurrence route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine

def TapeData.counter (data : TapeData) : CounterStage → List Unit
  | .vertexClauses => data.clauseCount
  | .vertexLiteralsFirst | .vertexLiteralsSecond |
      .edgeLiteralsFirst | .edgeLiteralsSecond | .edgeLiteralsThird |
      .sourceLiterals => data.literalCount
  | .edgeIndex => data.edgeIndex
  | .sourceClauses => data.clauseIndex

def TapeData.setCounter (data : TapeData)
    (stage : CounterStage) (value : List Unit) : TapeData :=
  match stage with
  | .vertexClauses => { data with clauseCount := value }
  | .vertexLiteralsFirst | .vertexLiteralsSecond |
      .edgeLiteralsFirst | .edgeLiteralsSecond | .edgeLiteralsThird |
      .sourceLiterals => { data with literalCount := value }
  | .edgeIndex => { data with edgeIndex := value }
  | .sourceClauses => { data with clauseIndex := value }

@[simp] theorem TapeData.counter_setCounter (data : TapeData)
    (stage : CounterStage) (value : List Unit) :
    (data.setCounter stage value).counter stage = value := by
  cases stage <;> rfl

def CounterStage.units (stage : CounterStage)
    (value : List Unit) : List (Alphabet stage.stack) := by
  cases stage <;> exact value

@[simp] theorem CounterStage.units_nil (stage : CounterStage) :
    stage.units [] = [] := by
  cases stage <;> rfl

@[simp] theorem CounterStage.units_cons (stage : CounterStage)
    (value : List Unit) :
    stage.units (() :: value) = stage.unit :: stage.units value := by
  cases stage <;> rfl

theorem tapes_counter (data : TapeData) (stage : CounterStage) :
    tapes data stage.stack =
      stage.units (data.counter stage) := by
  cases stage <;> rfl

@[simp] theorem update_tapes_counter (data : TapeData)
    (stage : CounterStage) (value : List Unit) :
    Function.update (tapes data) stage.stack
        (stage.units value) =
      tapes (data.setCounter stage value) := by
  cases stage <;>
    simp [CounterStage.stack, CounterStage.units, TapeData.setCounter]

/-- Configuration reached when one copied counter has been fully restored. -/
def afterCounterCfg (stage : CounterStage) (cursor : Cursor)
    (data : TapeData) : machine.Cfg :=
  match stage with
  | .vertexClauses => copyCounterCfg .vertexLiteralsFirst cursor data
  | .vertexLiteralsFirst => copyCounterCfg .vertexLiteralsSecond cursor data
  | .vertexLiteralsSecond =>
      copyCounterCfg .edgeLiteralsFirst cursor
        { data with outputReverse := .atomEnd :: data.outputReverse }
  | .edgeLiteralsFirst => copyCounterCfg .edgeLiteralsSecond cursor data
  | .edgeLiteralsSecond => copyCounterCfg .edgeLiteralsThird cursor data
  | .edgeLiteralsThird =>
      copyCounterCfg .edgeIndex cursor
        { data with outputReverse := .atomEnd :: data.outputReverse }
  | .edgeIndex =>
      copyCounterCfg .sourceLiterals cursor
        { data with outputReverse := .atomEnd :: data.outputReverse }
  | .sourceLiterals => copyCounterCfg .sourceClauses cursor data
  | .sourceClauses =>
      scanTargetCfg cursor
        { data with outputReverse := .atomEnd :: data.outputReverse }

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine
