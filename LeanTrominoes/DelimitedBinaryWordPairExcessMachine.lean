/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairs
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.UnaryFieldEncoderMachine

/-! # Finite machine for unary excesses of delimited word pairs -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPairExcessMachine

open DelimitedBinaryWordPairs

/-- Selected truncated length difference for one word pair. -/
def excess (keepFirst : Bool) (first second : List Bool) : Nat :=
  if keepFirst then first.length - second.length
  else second.length - first.length

/-- One selected excess for every delimiter-encoded word pair. -/
def excesses (keepFirst : Bool) (input : Input) : List Nat :=
  input.pairs.map fun pair => excess keepFirst pair.1 pair.2

inductive Stack
  | input
  | first
  | second
  | outputReverse
  | output
  deriving DecidableEq, Fintype

inductive Label
  | scan
  | readFirst
  | readSecond
  | cancel
  | drainFirst (emit : Bool)
  | drainSecond (emit : Bool)
  | emitDelimiter
  | reverseOutput
  deriving Fintype

structure State where
  token : Option Token
  first : Option Bool
  second : Option Bool
  output : Option UnaryFieldEncoderMachine.Symbol
  deriving DecidableEq, Fintype

def initialState : State := ⟨none, none, none, none⟩

instance : Inhabited State := ⟨initialState⟩

abbrev Alphabet : Stack → Type
  | .input => Token
  | .first | .second => Bool
  | .outputReverse | .output => UnaryFieldEncoderMachine.Symbol

def setToken (state : State) (token : Option Token) : State :=
  { state with token := token }

def setFirst (state : State) (first : Option Bool) : State :=
  { state with first := first }

def setSecond (state : State) (second : Option Bool) : State :=
  { state with second := second }

def setOutput (state : State)
    (output : Option UnaryFieldEncoderMachine.Symbol) : State :=
  { state with output := output }

def tokenIsNone (state : State) : Bool := state.token.isNone

def tokenIsFirstBit (state : State) : Bool :=
  match state.token with
  | some (.firstBit _) => true
  | _ => false

def tokenIsSecondBit (state : State) : Bool :=
  match state.token with
  | some (.secondBit _) => true
  | _ => false

def tokenBitFromState (state : State) : Bool :=
  match state.token with
  | some (.firstBit bit) | some (.secondBit bit) => bit
  | _ => false

def bothPresent (state : State) : Bool :=
  state.first.isSome && state.second.isSome

def bothAbsent (state : State) : Bool :=
  state.first.isNone && state.second.isNone

def firstPresent (state : State) : Bool := state.first.isSome

def clearToken (state : State) : State := { state with token := none }

def clearPair (state : State) : State :=
  { state with first := none, second := none }

def clearOutput (state : State) : State := { state with output := none }

def outputFromState (state : State) : UnaryFieldEncoderMachine.Symbol :=
  state.output.getD .delimiter

def program (keepFirst : Bool) : Label → TM2.Stmt Alphabet Label State
  | .scan =>
      .pop .input setToken
        (.branch tokenIsNone
          (.goto fun _ => .reverseOutput)
          (.load clearToken (.goto fun _ => .readFirst)))
  | .readFirst =>
      .pop .input setToken
        (.branch tokenIsFirstBit
          (.push .first tokenBitFromState
            (.load clearToken (.goto fun _ => .readFirst)))
          (.load clearToken (.goto fun _ => .readSecond)))
  | .readSecond =>
      .pop .input setToken
        (.branch tokenIsSecondBit
          (.push .second tokenBitFromState
            (.load clearToken (.goto fun _ => .readSecond)))
          (.load clearToken (.goto fun _ => .cancel)))
  | .cancel =>
      .pop .first setFirst
        (.pop .second setSecond
          (.branch bothPresent
            (.load clearPair (.goto fun _ => .cancel))
            (.branch bothAbsent
              (.load clearPair (.goto fun _ => .emitDelimiter))
              (.branch firstPresent
                (if keepFirst then
                  .push .outputReverse (fun _ => .unit)
                    (.load clearPair (.goto fun _ => .drainFirst true))
                else
                  .load clearPair (.goto fun _ => .drainFirst false))
                (if keepFirst then
                  .load clearPair (.goto fun _ => .drainSecond false)
                else
                  .push .outputReverse (fun _ => .unit)
                    (.load clearPair (.goto fun _ => .drainSecond true)))))))
  | .drainFirst emit =>
      .pop .first setFirst
        (.branch firstPresent
          (if emit then
            .push .outputReverse (fun _ => .unit)
              (.load clearPair (.goto fun _ => .drainFirst true))
          else
            .load clearPair (.goto fun _ => .drainFirst false))
          (.load clearPair (.goto fun _ => .emitDelimiter)))
  | .drainSecond emit =>
      .pop .second setSecond
        (.branch (fun state => state.second.isSome)
          (if emit then
            .push .outputReverse (fun _ => .unit)
              (.load clearPair (.goto fun _ => .drainSecond true))
          else
            .load clearPair (.goto fun _ => .drainSecond false))
          (.load clearPair (.goto fun _ => .emitDelimiter)))
  | .emitDelimiter =>
      .push .outputReverse (fun _ => .delimiter)
        (.goto fun _ => .scan)
  | .reverseOutput =>
      .pop .outputReverse setOutput
        (.branch (fun state => state.output.isNone)
          (.load clearOutput .halt)
          (.push .output outputFromState
            (.load clearOutput (.goto fun _ => .reverseOutput))))

abbrev machine (keepFirst : Bool) : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .scan
  σ := State
  initialState := initialState
  m := program keepFirst

structure TapeData where
  input : List Token
  first : List Bool
  second : List Bool
  outputReverse : List UnaryFieldEncoderMachine.Symbol
  output : List UnaryFieldEncoderMachine.Symbol

def tapes (data : TapeData) : ∀ stack, List (Alphabet stack)
  | .input => data.input
  | .first => data.first
  | .second => data.second
  | .outputReverse => data.outputReverse
  | .output => data.output

def cfg (label : Label) (state : State) (data : TapeData) :
    TM2.Cfg Alphabet Label State :=
  ⟨some label, state, tapes data⟩

def scanCfg (data : TapeData) := cfg .scan initialState data

def readFirstCfg (data : TapeData) := cfg .readFirst initialState data

def readSecondCfg (data : TapeData) := cfg .readSecond initialState data

def cancelCfg (data : TapeData) := cfg .cancel initialState data

def drainFirstCfg (emit : Bool) (data : TapeData) :=
  cfg (.drainFirst emit) initialState data

def drainSecondCfg (emit : Bool) (data : TapeData) :=
  cfg (.drainSecond emit) initialState data

def emitDelimiterCfg (data : TapeData) :=
  cfg .emitDelimiter initialState data

def reverseOutputCfg (data : TapeData) :=
  cfg .reverseOutput initialState data

def haltCfg (output : List UnaryFieldEncoderMachine.Symbol) :
    TM2.Cfg Alphabet Label State :=
  ⟨none, initialState, tapes ⟨[], [], [], [], output⟩⟩

def oneStep {keepFirst : Bool} {first last : TM2.Cfg Alphabet Label State}
    (step : TM2.step (program keepFirst) first = some last) :
    EvalsToInTime (TM2.step (program keepFirst)) first (some last) 1 :=
  FiniteBlockTransducer.oneStep step

end DelimitedBinaryWordPairExcessMachine
end LeanTrominoes
