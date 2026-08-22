/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryBlockRightRotationMachine

/-! # Tape configurations for unary block right rotation -/

namespace LeanTrominoes.UnaryBlockRightRotationMachine

open Turing

structure TapeData where
  input : List InputSymbol
  sizesReverse : List UnarySymbol
  sizes : List UnarySymbol
  startsReverse : List UnarySymbol
  starts : List UnarySymbol
  group : List Unit
  groupRemaining : List Unit
  start : List Unit
  startRestore : List Unit
  position : List Unit
  positionRestore : List Unit
  outputReverse : List UnarySymbol
  output : List UnarySymbol

def tapes (data : TapeData) : ∀ stack, List (Alphabet stack)
  | .input => data.input
  | .sizesReverse => data.sizesReverse
  | .sizes => data.sizes
  | .startsReverse => data.startsReverse
  | .starts => data.starts
  | .group => data.group
  | .groupRemaining => data.groupRemaining
  | .start => data.start
  | .startRestore => data.startRestore
  | .position => data.position
  | .positionRestore => data.positionRestore
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
def pushSizeReverseCfg (symbol : UnarySymbol) :=
  inputCfg .pushSizeReverse (.left symbol)
def scanRightCfg := emptyCfg .scanRight
def pushStartReverseCfg (symbol : UnarySymbol) :=
  inputCfg .pushStartReverse (.right symbol)
def restoreSizesCfg := emptyCfg .restoreSizes
def pushSizeCfg (symbol : UnarySymbol) := unaryCfg .pushSize symbol
def restoreStartsCfg := emptyCfg .restoreStarts
def pushStartCfg (symbol : UnarySymbol) := unaryCfg .pushStart symbol
def scanSizeFieldCfg := emptyCfg .scanSizeField
def pushGroupUnitCfg := emptyCfg .pushGroupUnit
def scanStartFieldCfg := emptyCfg .scanStartField
def pushStartUnitCfg := emptyCfg .pushStartUnit
def beginGroupCfg := emptyCfg .beginGroup
def copyFirstStartCfg := emptyCfg .copyFirstStart
def restoreFirstStartCfg := emptyCfg .restoreFirstStart
def copyFirstGroupCfg := emptyCfg .copyFirstGroup
def emitFirstDelimiterCfg := emptyCfg .emitFirstDelimiter
def beginRemainingCfg := emptyCfg .beginRemaining
def copyRemainingStartCfg := emptyCfg .copyRemainingStart
def restoreRemainingStartCfg := emptyCfg .restoreRemainingStart
def copyPositionCfg := emptyCfg .copyPosition
def restorePositionCfg := emptyCfg .restorePosition
def emitRemainingDelimiterCfg := emptyCfg .emitRemainingDelimiter
def clearStartCfg := emptyCfg .clearStart
def clearPositionCfg := emptyCfg .clearPosition
def reverseOutputCfg := emptyCfg .reverseOutput
def pushOutputCfg (symbol : UnarySymbol) := unaryCfg .pushOutput symbol

def haltCfg (output : List UnarySymbol) : machine.Cfg :=
  ⟨none, .empty,
    tapes ⟨[], [], [], [], [], [], [], [], [], [], [], [], output⟩⟩

def haltDataCfg (data : TapeData) : machine.Cfg :=
  ⟨none, .empty, tapes data⟩

@[simp] theorem update_tapes_input (data : TapeData)
    (value : List InputSymbol) :
    Function.update (tapes data) .input value =
      tapes { data with input := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_sizesReverse (data : TapeData)
    (value : List UnarySymbol) :
    Function.update (tapes data) .sizesReverse value =
      tapes { data with sizesReverse := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_sizes (data : TapeData)
    (value : List UnarySymbol) :
    Function.update (tapes data) .sizes value =
      tapes { data with sizes := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_startsReverse (data : TapeData)
    (value : List UnarySymbol) :
    Function.update (tapes data) .startsReverse value =
      tapes { data with startsReverse := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_starts (data : TapeData)
    (value : List UnarySymbol) :
    Function.update (tapes data) .starts value =
      tapes { data with starts := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_group (data : TapeData) (value : List Unit) :
    Function.update (tapes data) .group value =
      tapes { data with group := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_groupRemaining (data : TapeData)
    (value : List Unit) :
    Function.update (tapes data) .groupRemaining value =
      tapes { data with groupRemaining := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_start (data : TapeData) (value : List Unit) :
    Function.update (tapes data) .start value =
      tapes { data with start := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_startRestore (data : TapeData)
    (value : List Unit) :
    Function.update (tapes data) .startRestore value =
      tapes { data with startRestore := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_position (data : TapeData) (value : List Unit) :
    Function.update (tapes data) .position value =
      tapes { data with position := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_positionRestore (data : TapeData)
    (value : List Unit) :
    Function.update (tapes data) .positionRestore value =
      tapes { data with positionRestore := value } := by
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

end LeanTrominoes.UnaryBlockRightRotationMachine
