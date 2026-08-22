/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterCounterData

/-! # Counter-loop data for tagged source cycle-link route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

/-- Output units accumulated while a unary counter is copied. -/
def copiedOutput (counter : List Unit) : List OutputToken :=
  counter.reverse.map fun _ => .atomUnit

/-- Tape data after completely copying a counter into scratch and output. -/
def afterCopyData (data : TapeData) (stage : CounterStage)
    (counter : List Unit) : TapeData :=
  { data.setCounter stage [] with
    scratch := counter.reverse ++ data.scratch
    outputReverse := copiedOutput counter ++ data.outputReverse }

/-- Tape data after completely restoring a counter from scratch. -/
def afterRestoreData (data : TapeData) (stage : CounterStage)
    (scratch : List Unit) : TapeData :=
  { data.setCounter stage (scratch.reverse ++ data.counter stage) with
    scratch := [] }

/-- Tape data after a complete copy-and-restore round trip. -/
def afterCounterData (data : TapeData) (counter : List Unit) : TapeData :=
  { data with
    scratch := []
    outputReverse := copiedOutput counter ++ data.outputReverse }

@[simp] theorem TapeData.counter_setScratchOutputReverse (data : TapeData)
    (stage : CounterStage) (scratch : List Unit)
    (outputReverse : List OutputToken) :
    ({ data with
      scratch := scratch
      outputReverse := outputReverse }).counter stage =
        data.counter stage := by
  cases stage <;> rfl

@[simp] theorem afterCopyData_nil (data : TapeData)
    (stage : CounterStage) :
    afterCopyData data stage [] = data.setCounter stage [] := by
  cases stage <;> rfl

theorem afterCopyData_cons (data : TapeData) (stage : CounterStage)
    (remaining : List Unit) :
    afterCopyData
        { data.setCounter stage remaining with
          scratch := () :: data.scratch
          outputReverse := .atomUnit :: data.outputReverse }
        stage remaining =
      afterCopyData data stage (() :: remaining) := by
  cases stage <;>
    simp [afterCopyData, copiedOutput, TapeData.setCounter,
      List.reverse_cons, List.map_append, List.append_assoc]

@[simp] theorem afterRestoreData_nil (data : TapeData)
    (stage : CounterStage) :
    afterRestoreData data stage [] = { data with scratch := [] } := by
  cases stage <;> rfl

theorem afterRestoreData_cons (data : TapeData) (stage : CounterStage)
    (remaining : List Unit) :
    afterRestoreData
        { data.setCounter stage (() :: data.counter stage) with
          scratch := remaining }
        stage remaining =
      afterRestoreData data stage (() :: remaining) := by
  cases stage <;>
    simp [afterRestoreData, TapeData.counter, TapeData.setCounter,
      List.reverse_cons, List.append_assoc]

theorem afterRestoreData_afterCopyData (data : TapeData)
    (stage : CounterStage) (counter : List Unit)
    (counterEq : data.counter stage = counter)
    (scratchEq : data.scratch = []) :
    afterRestoreData (afterCopyData data stage counter) stage
        counter.reverse =
      afterCounterData data counter := by
  cases stage <;>
    simp only [TapeData.counter] at counterEq <;>
    simp [afterRestoreData, afterCopyData, afterCounterData,
      TapeData.counter, TapeData.setCounter, copiedOutput,
      counterEq, scratchEq]

end LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
