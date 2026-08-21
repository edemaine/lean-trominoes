/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

import LeanTrominoes.DelimitedBinaryWordPrefixTrueCounts
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.UnaryFieldEncoderMachine

/-! # Machine for true counts in successively longer row prefixes -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPrefixTrueCountMachine

abbrev Token := DelimitedBinaryWords.Token
abbrev OutputSymbol := UnaryFieldEncoderMachine.Symbol

inductive Stack
  | input
  | rowIndex
  | indexRestore
  | prefixCountdown
  | outputReverse
  | output
  deriving DecidableEq, Fintype

inductive Label
  | scanStart
  | copyIndex
  | restoreIndex
  | scanPrefix
  | scanSuffix
  | clearPrefix
  | finishRow
  | clearRowIndex
  | reverseOutput
  deriving Fintype

structure State where
  token : Option Token
  outputSymbol : Option OutputSymbol
  present : Bool
  deriving DecidableEq, Fintype

def initialState : State := ⟨none, none, false⟩

instance : Inhabited State := ⟨initialState⟩

abbrev Alphabet : Stack → Type
  | .input => Token
  | .rowIndex | .indexRestore | .prefixCountdown => Unit
  | .outputReverse | .output => OutputSymbol

def setToken (state : State) (token : Option Token) : State :=
  { state with token := token }

def setOutputSymbol (state : State)
    (symbol : Option OutputSymbol) : State :=
  { state with outputSymbol := symbol }

def setPresent (state : State) (unit : Option Unit) : State :=
  { state with present := unit.isSome }

def clearToken (state : State) : State :=
  { state with token := none }

def clearOutputSymbol (state : State) : State :=
  { state with outputSymbol := none }

def clearPresent (state : State) : State :=
  { state with present := false }

def tokenIsNone (state : State) : Bool := state.token.isNone
def outputSymbolIsNone (state : State) : Bool := state.outputSymbol.isNone
def isPresent (state : State) : Bool := state.present

def tokenIsEnd (state : State) : Bool :=
  match state.token with
  | some .wordEnd => true
  | _ => false

def tokenIsTrue (state : State) : Bool :=
  match state.token with
  | some (.bit true) => true
  | _ => false

def outputSymbolFromState (state : State) : OutputSymbol :=
  state.outputSymbol.getD .delimiter

def program : Label → TM2.Stmt Alphabet Label State
  | .scanStart =>
      .pop .input setToken
        (.branch tokenIsNone
          (.load clearToken (.goto fun _ => .clearRowIndex))
          (.load clearToken (.goto fun _ => .copyIndex)))
  | .copyIndex =>
      .pop .rowIndex setPresent
        (.branch isPresent
          (.push .indexRestore (fun _ => ())
            (.push .prefixCountdown (fun _ => ())
              (.load clearPresent (.goto fun _ => .copyIndex))))
          (.load clearPresent (.goto fun _ => .restoreIndex)))
  | .restoreIndex =>
      .pop .indexRestore setPresent
        (.branch isPresent
          (.push .rowIndex (fun _ => ())
            (.load clearPresent (.goto fun _ => .restoreIndex)))
          (.load clearPresent (.goto fun _ => .scanPrefix)))
  | .scanPrefix =>
      .pop .prefixCountdown setPresent
        (.branch isPresent
          (.pop .input setToken
            (.branch tokenIsNone
              (.load clearToken
                (.load clearPresent (.goto fun _ => .clearPrefix)))
              (.branch tokenIsEnd
                (.load clearToken
                  (.load clearPresent (.goto fun _ => .clearPrefix)))
                (.branch tokenIsTrue
                  (.push .outputReverse (fun _ => .unit)
                    (.load clearToken
                      (.load clearPresent (.goto fun _ => .scanPrefix))))
                  (.load clearToken
                    (.load clearPresent (.goto fun _ => .scanPrefix)))))))
          (.load clearPresent (.goto fun _ => .scanSuffix)))
  | .scanSuffix =>
      .pop .input setToken
        (.branch tokenIsNone
          (.load clearToken (.goto fun _ => .finishRow))
          (.branch tokenIsEnd
            (.load clearToken (.goto fun _ => .finishRow))
            (.load clearToken (.goto fun _ => .scanSuffix))))
  | .clearPrefix =>
      .pop .prefixCountdown setPresent
        (.branch isPresent
          (.load clearPresent (.goto fun _ => .clearPrefix))
          (.load clearPresent (.goto fun _ => .finishRow)))
  | .finishRow =>
      .push .outputReverse (fun _ => .delimiter)
        (.push .rowIndex (fun _ => ())
          (.goto fun _ => .scanStart))
  | .clearRowIndex =>
      .pop .rowIndex setPresent
        (.branch isPresent
          (.load clearPresent (.goto fun _ => .clearRowIndex))
          (.load clearPresent (.goto fun _ => .reverseOutput)))
  | .reverseOutput =>
      .pop .outputReverse setOutputSymbol
        (.branch outputSymbolIsNone
          .halt
          (.push .output outputSymbolFromState
            (.load clearOutputSymbol (.goto fun _ => .reverseOutput))))

abbrev machine : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .scanStart
  σ := State
  initialState := initialState
  m := program

structure TapeData where
  input : List Token
  rowIndex : List Unit
  indexRestore : List Unit
  prefixCountdown : List Unit
  outputReverse : List OutputSymbol
  output : List OutputSymbol

def tapes (data : TapeData) : ∀ stack, List (Alphabet stack)
  | .input => data.input
  | .rowIndex => data.rowIndex
  | .indexRestore => data.indexRestore
  | .prefixCountdown => data.prefixCountdown
  | .outputReverse => data.outputReverse
  | .output => data.output

def cfg (label : Label) (state : State) (data : TapeData) :
    TM2.Cfg Alphabet Label State :=
  ⟨some label, state, tapes data⟩

def idleCfg (label : Label) (data : TapeData) :=
  cfg label initialState data

def scanStartCfg := idleCfg .scanStart
def copyIndexCfg := idleCfg .copyIndex
def restoreIndexCfg := idleCfg .restoreIndex
def scanPrefixCfg := idleCfg .scanPrefix
def scanSuffixCfg := idleCfg .scanSuffix
def clearPrefixCfg := idleCfg .clearPrefix
def finishRowCfg := idleCfg .finishRow
def clearRowIndexCfg := idleCfg .clearRowIndex
def reverseOutputCfg := idleCfg .reverseOutput

def haltCfg (output : List OutputSymbol) :
    TM2.Cfg Alphabet Label State :=
  ⟨none, initialState, tapes ⟨[], [], [], [], [], output⟩⟩

end DelimitedBinaryWordPrefixTrueCountMachine
end LeanTrominoes
