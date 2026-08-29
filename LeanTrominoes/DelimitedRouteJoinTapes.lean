/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedRouteJoinMachine

/-! # Tape configurations for delimited-route joining -/

namespace LeanTrominoes.DelimitedRouteJoin

open Turing

structure TapeData where
  input : List InputSymbol
  prefixReverse : List Token
  prefixes : List Token
  suffixReverse : List Token
  suffixes : List Token
  outputReverse : List Token
  output : List Token

def tapes (data : TapeData) : ∀ stack, List (Alphabet stack)
  | .input => data.input
  | .prefixReverse => data.prefixReverse
  | .prefixes => data.prefixes
  | .suffixReverse => data.suffixReverse
  | .suffixes => data.suffixes
  | .outputReverse => data.outputReverse
  | .output => data.output

def cfg (label : Label) (state : State) (data : TapeData) : machine.Cfg :=
  ⟨some label, state, tapes data⟩

def emptyCfg (label : Label) (data : TapeData) : machine.Cfg :=
  cfg label .empty data

def inputCfg (label : Label) (symbol : InputSymbol) (data : TapeData) :
    machine.Cfg :=
  cfg label (.input (some symbol)) data

def tokenCfg (label : Label) (token : Token) (data : TapeData) :
    machine.Cfg :=
  cfg label (.token (some token)) data

def scanLeftCfg := emptyCfg .scanLeft
def pushPrefixReverseCfg (token : Token) :=
  inputCfg .pushPrefixReverse (.left token)
def scanRightCfg := emptyCfg .scanRight
def pushSuffixReverseCfg (token : Token) :=
  inputCfg .pushSuffixReverse (.right token)
def restorePrefixesCfg := emptyCfg .restorePrefixes
def pushPrefixCfg (token : Token) := tokenCfg .pushPrefix token
def restoreSuffixesCfg := emptyCfg .restoreSuffixes
def pushSuffixCfg (token : Token) := tokenCfg .pushSuffix token
def scanPrefixCfg := emptyCfg .scanPrefix
def pushPrefixTokenCfg (token : Token) := tokenCfg .pushPrefixToken token
def scanSuffixCfg := emptyCfg .scanSuffix
def pushSuffixTokenCfg (token : Token) := tokenCfg .pushSuffixToken token
def cleanupPrefixesCfg := emptyCfg .cleanupPrefixes
def cleanupSuffixesCfg := emptyCfg .cleanupSuffixes
def reverseOutputCfg := emptyCfg .reverseOutput
def pushOutputCfg (token : Token) := tokenCfg .pushOutput token

def haltCfg (output : List Token) : machine.Cfg :=
  ⟨none, .empty, tapes ⟨[], [], [], [], [], [], output⟩⟩

@[simp] theorem update_tapes_input (data : TapeData)
    (value : List InputSymbol) :
    Function.update (tapes data) .input value =
      tapes { data with input := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_prefixReverse (data : TapeData)
    (value : List Token) :
    Function.update (tapes data) .prefixReverse value =
      tapes { data with prefixReverse := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_prefixes (data : TapeData)
    (value : List Token) :
    Function.update (tapes data) .prefixes value =
      tapes { data with prefixes := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_suffixReverse (data : TapeData)
    (value : List Token) :
    Function.update (tapes data) .suffixReverse value =
      tapes { data with suffixReverse := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_suffixes (data : TapeData)
    (value : List Token) :
    Function.update (tapes data) .suffixes value =
      tapes { data with suffixes := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_outputReverse (data : TapeData)
    (value : List Token) :
    Function.update (tapes data) .outputReverse value =
      tapes { data with outputReverse := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_output (data : TapeData)
    (value : List Token) :
    Function.update (tapes data) .output value =
      tapes { data with output := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

end LeanTrominoes.DelimitedRouteJoin
