/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryAlignedAddMachine

/-! # Tape configurations for aligned unary addition -/

namespace LeanTrominoes
namespace UnaryAlignedAddMachine

open Turing

structure TapeData where
  input : List InputSymbol
  firstReverse : List UnarySymbol
  firsts : List UnarySymbol
  secondReverse : List UnarySymbol
  seconds : List UnarySymbol
  outputReverse : List UnarySymbol
  output : List UnarySymbol

def tapes (data : TapeData) : ∀ stack, List (Alphabet stack)
  | .input => data.input
  | .firstReverse => data.firstReverse
  | .firsts => data.firsts
  | .secondReverse => data.secondReverse
  | .seconds => data.seconds
  | .outputReverse => data.outputReverse
  | .output => data.output

def cfg (label : Label) (state : State) (data : TapeData) : machine.Cfg :=
  ⟨some label, state, tapes data⟩

def emptyCfg (label : Label) (data : TapeData) : machine.Cfg :=
  cfg label .empty data

def inputCfg (label : Label) (symbol : InputSymbol) (data : TapeData) :
    machine.Cfg :=
  cfg label (.input (some symbol)) data

def unaryCfg (label : Label) (symbol : UnarySymbol) (data : TapeData) :
    machine.Cfg :=
  cfg label (.unary (some symbol)) data

def scanLeftCfg := emptyCfg .scanLeft
def pushFirstReverseCfg (symbol : UnarySymbol) :=
  inputCfg .pushFirstReverse (.left symbol)
def scanRightCfg := emptyCfg .scanRight
def pushSecondReverseCfg (symbol : UnarySymbol) :=
  inputCfg .pushSecondReverse (.right symbol)
def restoreFirstsCfg := emptyCfg .restoreFirsts
def pushFirstCfg (symbol : UnarySymbol) := unaryCfg .pushFirst symbol
def restoreSecondsCfg := emptyCfg .restoreSeconds
def pushSecondCfg (symbol : UnarySymbol) := unaryCfg .pushSecond symbol
def scanFirstFieldCfg := emptyCfg .scanFirstField
def pushFirstUnitCfg := emptyCfg .pushFirstUnit
def scanSecondFieldCfg := emptyCfg .scanSecondField
def pushSecondUnitCfg := emptyCfg .pushSecondUnit
def emitDelimiterCfg := emptyCfg .emitDelimiter
def reverseOutputCfg := emptyCfg .reverseOutput
def pushOutputCfg (symbol : UnarySymbol) := unaryCfg .pushOutput symbol

def haltCfg (output : List UnarySymbol) : machine.Cfg :=
  ⟨none, .empty, tapes ⟨[], [], [], [], [], [], output⟩⟩

def haltDataCfg (data : TapeData) : machine.Cfg :=
  ⟨none, .empty, tapes data⟩

@[simp] theorem update_tapes_input (data : TapeData)
    (value : List InputSymbol) :
    Function.update (tapes data) .input value =
      tapes { data with input := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_firstReverse (data : TapeData)
    (value : List UnarySymbol) :
    Function.update (tapes data) .firstReverse value =
      tapes { data with firstReverse := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_firsts (data : TapeData)
    (value : List UnarySymbol) :
    Function.update (tapes data) .firsts value =
      tapes { data with firsts := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_secondReverse (data : TapeData)
    (value : List UnarySymbol) :
    Function.update (tapes data) .secondReverse value =
      tapes { data with secondReverse := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_seconds (data : TapeData)
    (value : List UnarySymbol) :
    Function.update (tapes data) .seconds value =
      tapes { data with seconds := value } := by
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

end UnaryAlignedAddMachine
end LeanTrominoes
