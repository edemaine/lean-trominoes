/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterCounterTapeUpdates
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterOutputTapeUpdates

/-! # Uniform counter data for tagged source cycle-link route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

def TapeData.counter (data : TapeData) : CounterStage → List Unit
  | .sourceVertexClause | .sourceSourceClause |
      .targetVertexClause | .targetSourceClause => data.clauseCount
  | .sourceVertexLiteralFirst | .sourceVertexLiteralSecond |
      .sourceEdgeLiteralFirst | .sourceEdgeLiteralSecond |
      .sourceEdgeLiteralThird | .sourceEdgeIndexLiteral |
      .sourceSourceLiteral | .targetVertexLiteralFirst |
      .targetVertexLiteralSecond | .targetEdgeLiteralFirst |
      .targetEdgeLiteralSecond | .targetEdgeLiteralThird |
      .targetEdgeIndexLiteral | .targetSourceLiteral => data.literalCount
  | .sourceEdgeIndexFirst | .sourceEdgeIndexSecond |
      .sourceSourceIndex | .targetEdgeIndexFirst |
      .targetEdgeIndexSecond | .targetSourceIndex |
      .targetTargetIndex => data.linkIndex

def TapeData.setCounter (data : TapeData) (stage : CounterStage)
    (value : List Unit) : TapeData :=
  match stage with
  | .sourceVertexClause | .sourceSourceClause |
      .targetVertexClause | .targetSourceClause =>
      { data with clauseCount := value }
  | .sourceVertexLiteralFirst | .sourceVertexLiteralSecond |
      .sourceEdgeLiteralFirst | .sourceEdgeLiteralSecond |
      .sourceEdgeLiteralThird | .sourceEdgeIndexLiteral |
      .sourceSourceLiteral | .targetVertexLiteralFirst |
      .targetVertexLiteralSecond | .targetEdgeLiteralFirst |
      .targetEdgeLiteralSecond | .targetEdgeLiteralThird |
      .targetEdgeIndexLiteral | .targetSourceLiteral =>
      { data with literalCount := value }
  | .sourceEdgeIndexFirst | .sourceEdgeIndexSecond |
      .sourceSourceIndex | .targetEdgeIndexFirst |
      .targetEdgeIndexSecond | .targetSourceIndex |
      .targetTargetIndex => { data with linkIndex := value }

@[simp] theorem TapeData.counter_setCounter (data : TapeData)
    (stage : CounterStage) (value : List Unit) :
    (data.setCounter stage value).counter stage = value := by
  cases stage <;> rfl

@[simp] theorem TapeData.scratch_setCounter (data : TapeData)
    (stage : CounterStage) (value : List Unit) :
    (data.setCounter stage value).scratch = data.scratch := by
  cases stage <;> rfl

@[simp] theorem TapeData.outputReverse_setCounter (data : TapeData)
    (stage : CounterStage) (value : List Unit) :
    (data.setCounter stage value).outputReverse = data.outputReverse := by
  cases stage <;> rfl

@[simp] theorem TapeData.counter_setScratch (data : TapeData)
    (stage : CounterStage) (value : List Unit) :
    ({ data with scratch := value }).counter stage = data.counter stage := by
  cases stage <;> rfl

theorem TapeData.setCounter_setScratch (data : TapeData)
    (stage : CounterStage) (counter scratch : List Unit) :
    ({ data with scratch := scratch }).setCounter stage counter =
      { data.setCounter stage counter with scratch := scratch } := by
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
    tapes data stage.stack = stage.units (data.counter stage) := by
  cases stage <;> rfl

@[simp] theorem update_tapes_counter (data : TapeData)
    (stage : CounterStage) (value : List Unit) :
    Function.update (tapes data) stage.stack (stage.units value) =
      tapes (data.setCounter stage value) := by
  cases stage <;>
    simp [CounterStage.stack, CounterStage.units, TapeData.setCounter]

/-- Configuration reached when one copied counter has been fully restored. -/
def afterCounterCfg (stage : CounterStage) (tag : Tag)
    (data : TapeData) : machine.Cfg :=
  match stage with
  | .sourceVertexClause =>
      copyCounterCfg .sourceVertexLiteralFirst tag data
  | .sourceVertexLiteralFirst =>
      copyCounterCfg .sourceVertexLiteralSecond tag data
  | .sourceVertexLiteralSecond =>
      copyCounterCfg .sourceEdgeLiteralFirst tag
        { data with outputReverse := .atomEnd :: data.outputReverse }
  | .sourceEdgeLiteralFirst =>
      copyCounterCfg .sourceEdgeLiteralSecond tag data
  | .sourceEdgeLiteralSecond =>
      copyCounterCfg .sourceEdgeLiteralThird tag data
  | .sourceEdgeLiteralThird =>
      copyCounterCfg .sourceEdgeIndexLiteral tag
        { data with outputReverse := .atomEnd :: data.outputReverse }
  | .sourceEdgeIndexLiteral =>
      copyCounterCfg .sourceEdgeIndexFirst tag data
  | .sourceEdgeIndexFirst =>
      copyCounterCfg .sourceEdgeIndexSecond tag data
  | .sourceEdgeIndexSecond =>
      copyCounterCfg .sourceSourceLiteral tag
        { data with outputReverse := .atomEnd :: data.outputReverse }
  | .sourceSourceLiteral =>
      copyCounterCfg .sourceSourceClause tag data
  | .sourceSourceClause =>
      copyCounterCfg .sourceSourceIndex tag data
  | .sourceSourceIndex =>
      scanTargetCfg tag
        { data with outputReverse := .atomEnd :: data.outputReverse }
  | .targetVertexClause =>
      copyCounterCfg .targetVertexLiteralFirst tag data
  | .targetVertexLiteralFirst =>
      copyCounterCfg .targetVertexLiteralSecond tag data
  | .targetVertexLiteralSecond =>
      copyCounterCfg .targetEdgeLiteralFirst tag
        { data with outputReverse := .atomEnd :: data.outputReverse }
  | .targetEdgeLiteralFirst =>
      copyCounterCfg .targetEdgeLiteralSecond tag data
  | .targetEdgeLiteralSecond =>
      copyCounterCfg .targetEdgeLiteralThird tag data
  | .targetEdgeLiteralThird =>
      copyCounterCfg .targetEdgeIndexLiteral tag
        { data with outputReverse := .atomEnd :: data.outputReverse }
  | .targetEdgeIndexLiteral =>
      copyCounterCfg .targetEdgeIndexFirst tag data
  | .targetEdgeIndexFirst =>
      copyCounterCfg .targetEdgeIndexSecond tag data
  | .targetEdgeIndexSecond =>
      copyCounterCfg .targetSourceLiteral tag
        { data with outputReverse :=
            .atomEnd :: .atomUnit :: data.outputReverse }
  | .targetSourceLiteral =>
      copyCounterCfg .targetSourceClause tag data
  | .targetSourceClause =>
      copyCounterCfg .targetSourceIndex tag data
  | .targetSourceIndex =>
      copyCounterCfg .targetTargetIndex tag
        { data with outputReverse := .atomEnd :: data.outputReverse }
  | .targetTargetIndex => finishTargetRecordCfg tag data

end LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
