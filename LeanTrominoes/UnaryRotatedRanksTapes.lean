/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryRotatedRanksMachine

/-! # Tape configurations for unary rotated ranks -/

namespace LeanTrominoes
namespace UnaryRotatedRanksMachine

open Turing

structure TapeData where
  input : List InputSymbol
  rankReverse : List UnarySymbol
  ranks : List UnarySymbol
  sizeReverse : List UnarySymbol
  sizes : List UnarySymbol
  outputReverse : List UnarySymbol
  output : List UnarySymbol

def tapes (data : TapeData) : ∀ stack, List (Alphabet stack)
  | .input => data.input
  | .rankReverse => data.rankReverse
  | .ranks => data.ranks
  | .sizeReverse => data.sizeReverse
  | .sizes => data.sizes
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
def pushRankReverseCfg (symbol : UnarySymbol) :=
  inputCfg .pushRankReverse (.left symbol)
def scanRightCfg := emptyCfg .scanRight
def pushSizeReverseCfg (symbol : UnarySymbol) :=
  inputCfg .pushSizeReverse (.right symbol)
def restoreRanksCfg := emptyCfg .restoreRanks
def pushRankCfg (symbol : UnarySymbol) := unaryCfg .pushRank symbol
def restoreSizesCfg := emptyCfg .restoreSizes
def pushSizeCfg (symbol : UnarySymbol) := unaryCfg .pushSize symbol
def scanRankCfg := emptyCfg .scanRank
def positiveRankRestCfg := emptyCfg .positiveRankRest
def pushPositiveUnitCfg := emptyCfg .pushPositiveUnit
def zeroRankFirstSizeCfg := emptyCfg .zeroRankFirstSize
def zeroRankRestSizeCfg := emptyCfg .zeroRankRestSize
def pushZeroUnitCfg := emptyCfg .pushZeroUnit
def drainSizeCfg := emptyCfg .drainSize
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

@[simp] theorem update_tapes_rankReverse (data : TapeData)
    (value : List UnarySymbol) :
    Function.update (tapes data) .rankReverse value =
      tapes { data with rankReverse := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_ranks (data : TapeData)
    (value : List UnarySymbol) :
    Function.update (tapes data) .ranks value =
      tapes { data with ranks := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_sizeReverse (data : TapeData)
    (value : List UnarySymbol) :
    Function.update (tapes data) .sizeReverse value =
      tapes { data with sizeReverse := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_sizes (data : TapeData)
    (value : List UnarySymbol) :
    Function.update (tapes data) .sizes value =
      tapes { data with sizes := value } := by
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

end UnaryRotatedRanksMachine
end LeanTrominoes
