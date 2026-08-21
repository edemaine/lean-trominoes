/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.RepresentativeEqualityRows

/-! # Finite machine filtering stable representative equality rows -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace RepresentativeEqualityRowsMachine

abbrev Token := DelimitedBinaryWords.Token

inductive Stack
  | input
  | rowIndex
  | indexRestore
  | prefixCountdown
  | rowReverse
  | rowForward
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
  | moveSelectedToForward
  | moveSelectedToOutput
  | clearRejectedRow
  | clearRowIndex
  | reverseOutput
  deriving Fintype

structure State where
  token : Option Token
  present : Bool
  representative : Bool
  deriving DecidableEq, Fintype

def initialState : State := ⟨none, false, true⟩

instance : Inhabited State := ⟨initialState⟩

abbrev Alphabet : Stack → Type
  | .input | .rowReverse | .rowForward | .outputReverse | .output => Token
  | .rowIndex | .indexRestore | .prefixCountdown => Unit

def setToken (state : State) (token : Option Token) : State :=
  { state with token := token }

def setPresent (state : State) (unit : Option Unit) : State :=
  { state with present := unit.isSome }

def clearToken (state : State) : State :=
  { state with token := none }

def clearPresent (state : State) : State :=
  { state with present := false }

def beginRow (state : State) : State :=
  { state with token := none, present := false, representative := true }

def inspectPrefixToken (state : State) : State :=
  { state with
    token := none
    present := false
    representative :=
      match state.token with
      | some (.bit true) => false
      | _ => state.representative }

def tokenIsNone (state : State) : Bool := state.token.isNone

def tokenIsEnd (state : State) : Bool :=
  match state.token with
  | some .wordEnd => true
  | _ => false

def isPresent (state : State) : Bool := state.present

def isRepresentative (state : State) : Bool := state.representative

def tokenFromState (state : State) : Token :=
  state.token.getD .wordStart

def program : Label → TM2.Stmt Alphabet Label State
  | .scanStart =>
      .pop .input setToken
        (.branch tokenIsNone
          (.load clearToken (.goto fun _ => .clearRowIndex))
          (.push .rowReverse tokenFromState
            (.load beginRow (.goto fun _ => .copyIndex))))
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
      .pop .input setToken
        (.branch tokenIsNone
          (.load clearToken (.goto fun _ => .clearPrefix))
          (.branch tokenIsEnd
            (.push .rowReverse tokenFromState
              (.load clearToken (.goto fun _ => .clearPrefix)))
            (.push .rowReverse tokenFromState
              (.pop .prefixCountdown setPresent
                (.branch isPresent
                  (.load inspectPrefixToken (.goto fun _ => .scanPrefix))
                  (.load inspectPrefixToken (.goto fun _ => .scanSuffix)))))))
  | .scanSuffix =>
      .pop .input setToken
        (.branch tokenIsNone
          (.load clearToken (.goto fun _ => .finishRow))
          (.branch tokenIsEnd
            (.push .rowReverse tokenFromState
              (.load clearToken (.goto fun _ => .finishRow)))
            (.push .rowReverse tokenFromState
              (.load clearToken (.goto fun _ => .scanSuffix)))))
  | .clearPrefix =>
      .pop .prefixCountdown setPresent
        (.branch isPresent
          (.load clearPresent (.goto fun _ => .clearPrefix))
          (.load clearPresent (.goto fun _ => .finishRow)))
  | .finishRow =>
      .branch isRepresentative
        (.goto fun _ => .moveSelectedToForward)
        (.goto fun _ => .clearRejectedRow)
  | .moveSelectedToForward =>
      .pop .rowReverse setToken
        (.branch tokenIsNone
          (.load clearToken (.goto fun _ => .moveSelectedToOutput))
          (.push .rowForward tokenFromState
            (.load clearToken (.goto fun _ => .moveSelectedToForward))))
  | .moveSelectedToOutput =>
      .pop .rowForward setToken
        (.branch tokenIsNone
          (.push .rowIndex (fun _ => ())
            (.load clearToken (.goto fun _ => .scanStart)))
          (.push .outputReverse tokenFromState
            (.load clearToken (.goto fun _ => .moveSelectedToOutput))))
  | .clearRejectedRow =>
      .pop .rowReverse setToken
        (.branch tokenIsNone
          (.push .rowIndex (fun _ => ())
            (.load beginRow (.goto fun _ => .scanStart)))
          (.load clearToken (.goto fun _ => .clearRejectedRow)))
  | .clearRowIndex =>
      .pop .rowIndex setPresent
        (.branch isPresent
          (.load clearPresent (.goto fun _ => .clearRowIndex))
          (.load clearPresent (.goto fun _ => .reverseOutput)))
  | .reverseOutput =>
      .pop .outputReverse setToken
        (.branch tokenIsNone
          .halt
          (.push .output tokenFromState
            (.load clearToken (.goto fun _ => .reverseOutput))))

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
  rowReverse : List Token
  rowForward : List Token
  outputReverse : List Token
  output : List Token

def tapes (data : TapeData) : ∀ stack, List (Alphabet stack)
  | .input => data.input
  | .rowIndex => data.rowIndex
  | .indexRestore => data.indexRestore
  | .prefixCountdown => data.prefixCountdown
  | .rowReverse => data.rowReverse
  | .rowForward => data.rowForward
  | .outputReverse => data.outputReverse
  | .output => data.output

def cfg (label : Label) (state : State) (data : TapeData) :
    TM2.Cfg Alphabet Label State :=
  ⟨some label, state, tapes data⟩

def idleCfg (label : Label) (data : TapeData) :
    TM2.Cfg Alphabet Label State := cfg label initialState data

def scanStartCfg := idleCfg .scanStart
def copyIndexCfg := idleCfg .copyIndex
def restoreIndexCfg := idleCfg .restoreIndex
def scanPrefixCfg (representative : Bool) (data : TapeData) :=
  cfg .scanPrefix ⟨none, false, representative⟩ data
def scanSuffixCfg (representative : Bool) (data : TapeData) :=
  cfg .scanSuffix ⟨none, false, representative⟩ data
def clearPrefixCfg (representative : Bool) (data : TapeData) :=
  cfg .clearPrefix ⟨none, false, representative⟩ data
def finishRowCfg (representative : Bool) (data : TapeData) :=
  cfg .finishRow ⟨none, false, representative⟩ data
def moveSelectedToForwardCfg := idleCfg .moveSelectedToForward
def moveSelectedToOutputCfg := idleCfg .moveSelectedToOutput
def clearRejectedRowCfg := idleCfg .clearRejectedRow
def clearRowIndexCfg := idleCfg .clearRowIndex
def reverseOutputCfg := idleCfg .reverseOutput

def haltCfg (output : List Token) : TM2.Cfg Alphabet Label State :=
  ⟨none, initialState,
    tapes ⟨[], [], [], [], [], [], [], output⟩⟩

def oneStep {first last : TM2.Cfg Alphabet Label State}
    (step : TM2.step program first = some last) :
    EvalsToInTime (TM2.step program) first (some last) 1 :=
  FiniteBlockTransducer.oneStep step

end RepresentativeEqualityRowsMachine
end LeanTrominoes
