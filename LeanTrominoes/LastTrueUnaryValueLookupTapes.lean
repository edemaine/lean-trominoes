/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastTrueUnaryValueLookupMachine

/-! # Tape configurations for last-true unary lookup -/

namespace LeanTrominoes
namespace LastTrueUnaryValueLookupMachine

open Turing

structure TapeData where
  input : List InputSymbol
  rowsReverse : List RowSymbol
  rows : List RowSymbol
  valuesReverse : List UnarySymbol
  values : List UnarySymbol
  valuesRestore : List UnarySymbol
  candidate : List Unit
  outputReverse : List UnarySymbol
  output : List UnarySymbol

def tapes (data : TapeData) : ∀ stack, List (Alphabet stack)
  | .input => data.input
  | .rowsReverse => data.rowsReverse
  | .rows => data.rows
  | .valuesReverse => data.valuesReverse
  | .values => data.values
  | .valuesRestore => data.valuesRestore
  | .candidate => data.candidate
  | .outputReverse => data.outputReverse
  | .output => data.output

def cfg (label : Label) (state : State) (data : TapeData) :
    machine.Cfg :=
  ⟨some label, state, tapes data⟩

def emptyCfg (label : Label) (data : TapeData) : machine.Cfg :=
  cfg label initialState data

def rowBitState (selected : Bool) : State :=
  { initialState with row := some (.bit selected) }

def inputState (symbol : InputSymbol) : State :=
  { initialState with input := some symbol }

def rowState (symbol : RowSymbol) : State :=
  { initialState with row := some symbol }

def unaryState (symbol : UnarySymbol) : State :=
  { initialState with unary := some symbol }

def rowUnaryState (selected : Bool) (symbol : UnarySymbol) : State :=
  { initialState with
    row := some (.bit selected)
    unary := some symbol }

def rowBitCfg (label : Label) (selected : Bool) (data : TapeData) :
    machine.Cfg :=
  cfg label (rowBitState selected) data

def inputCfg (label : Label) (symbol : InputSymbol) (data : TapeData) :
    machine.Cfg :=
  cfg label (inputState symbol) data

def rowCfg (label : Label) (symbol : RowSymbol) (data : TapeData) :
    machine.Cfg :=
  cfg label (rowState symbol) data

def unaryCfg (label : Label) (symbol : UnarySymbol) (data : TapeData) :
    machine.Cfg :=
  cfg label (unaryState symbol) data

def rowUnaryCfg (label : Label) (selected : Bool)
    (symbol : UnarySymbol) (data : TapeData) : machine.Cfg :=
  cfg label (rowUnaryState selected symbol) data

def scanLeftCfg := emptyCfg .scanLeft
def pushRowReverseCfg (symbol : RowSymbol) :=
  inputCfg .pushRowReverse (.left symbol)
def scanRightCfg := emptyCfg .scanRight
def pushValueReverseCfg (symbol : UnarySymbol) :=
  inputCfg .pushValueReverse (.right symbol)
def restoreRowsCfg := emptyCfg .restoreRows
def pushRowCfg (symbol : RowSymbol) := rowCfg .pushRow symbol
def restoreInitialValuesCfg := emptyCfg .restoreInitialValues
def pushInitialValueCfg (symbol : UnarySymbol) :=
  unaryCfg .pushInitialValue symbol
def scanRowsCfg := emptyCfg .scanRows
def nextBitCfg := emptyCfg .nextBit
def prepareValueCfg (selected : Bool) := rowBitCfg .prepareValue selected
def clearCandidateCfg (selected : Bool) := rowBitCfg .clearCandidate selected
def readValueCfg (selected : Bool) := rowBitCfg .readValue selected
def pushValueRestoreCfg (selected : Bool) (symbol : UnarySymbol) :=
  rowUnaryCfg .pushValueRestore selected symbol
def pushCandidateUnitCfg :=
  rowUnaryCfg .pushCandidateUnit true .unit
def drainCandidateCfg := emptyCfg .drainCandidate
def pushOutputUnitCfg := emptyCfg .pushOutputUnit
def emitDelimiterCfg := emptyCfg .emitDelimiter
def restoreValuesCfg := emptyCfg .restoreValues
def pushRestoredValueCfg (symbol : UnarySymbol) :=
  unaryCfg .pushRestoredValue symbol
def reverseOutputCfg := emptyCfg .reverseOutput
def pushOutputCfg (symbol : UnarySymbol) := unaryCfg .pushOutput symbol

def haltCfg (output : List UnarySymbol) : machine.Cfg :=
  ⟨none, initialState, tapes ⟨[], [], [], [], [], [], [], [], output⟩⟩

@[simp] theorem update_tapes_input (data : TapeData)
    (value : List InputSymbol) :
    Function.update (tapes data) .input value =
      tapes { data with input := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_rowsReverse (data : TapeData)
    (value : List RowSymbol) :
    Function.update (tapes data) .rowsReverse value =
      tapes { data with rowsReverse := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_rows (data : TapeData)
    (value : List RowSymbol) :
    Function.update (tapes data) .rows value =
      tapes { data with rows := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_valuesReverse (data : TapeData)
    (value : List UnarySymbol) :
    Function.update (tapes data) .valuesReverse value =
      tapes { data with valuesReverse := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_values (data : TapeData)
    (value : List UnarySymbol) :
    Function.update (tapes data) .values value =
      tapes { data with values := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_valuesRestore (data : TapeData)
    (value : List UnarySymbol) :
    Function.update (tapes data) .valuesRestore value =
      tapes { data with valuesRestore := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_candidate (data : TapeData)
    (value : List Unit) :
    Function.update (tapes data) .candidate value =
      tapes { data with candidate := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_outputReverse (data : TapeData)
    (value : List UnarySymbol) :
    Function.update (tapes data) .outputReverse value =
      tapes { data with outputReverse := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_output (data : TapeData)
    (value : List UnarySymbol) :
    Function.update (tapes data) .output value =
      tapes { data with output := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

end LastTrueUnaryValueLookupMachine
end LeanTrominoes
