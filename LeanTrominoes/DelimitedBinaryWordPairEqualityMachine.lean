/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairs
import LeanTrominoes.FiniteBlockTransducer

/-! # Finite machine for delimited binary-word equality -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPairEqualityMachine

open DelimitedBinaryWordPairs

inductive Stack
  | input
  | first
  | second
  | resultReverse
  | output
  deriving DecidableEq, Fintype

inductive Label
  | scan
  | readFirst
  | readSecond
  | compare
  | reverse
  deriving Fintype

structure State where
  equal : Bool
  token : Option Token
  first : Option Bool
  second : Option Bool
  deriving DecidableEq, Fintype

def initialState : State := ⟨true, none, none, none⟩

instance : Inhabited State := ⟨initialState⟩

abbrev Alphabet : Stack → Type
  | .input => Token
  | .first | .second | .resultReverse | .output => Bool

def setToken (state : State) (token : Option Token) : State :=
  { state with token := token }

def setFirst (state : State) (first : Option Bool) : State :=
  { state with first := first }

def setSecond (state : State) (second : Option Bool) : State :=
  { state with second := second }

def tokenIsNone (state : State) : Bool := state.token.isNone

def tokenIsFirstBit (state : State) : Bool :=
  match state.token with
  | some (.firstBit _) => true
  | _ => false

def tokenIsSecondBit (state : State) : Bool :=
  match state.token with
  | some (.secondBit _) => true
  | _ => false

def bothWordsEmpty (state : State) : Bool :=
  state.first.isNone && state.second.isNone

def firstBitFromState (state : State) : Bool :=
  state.first.getD false

def tokenBitFromState (state : State) : Bool :=
  match state.token with
  | some (.firstBit bit) | some (.secondBit bit) => bit
  | _ => false

def equalityFromState (state : State) : Bool := state.equal

def clearToken (state : State) : State := { state with token := none }

def clearFirst (state : State) : State := { state with first := none }

def advanceCompare (state : State) : State :=
  { equal := state.equal && decide (state.first = state.second)
    token := none
    first := none
    second := none }

def program : Label → TM2.Stmt Alphabet Label State
  | .scan =>
      .pop .input setToken
        (.branch tokenIsNone
          (.goto fun _ => .reverse)
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
          (.load clearToken (.goto fun _ => .compare)))
  | .compare =>
      .pop .first setFirst
        (.pop .second setSecond
          (.branch bothWordsEmpty
            (.push .resultReverse equalityFromState
              (.load (fun _ => initialState) (.goto fun _ => .scan)))
            (.load advanceCompare (.goto fun _ => .compare))))
  | .reverse =>
      .pop .resultReverse setFirst
        (.branch (fun state => state.first.isNone)
          .halt
          (.push .output firstBitFromState
            (.load clearFirst (.goto fun _ => .reverse))))

abbrev machine : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .scan
  σ := State
  initialState := initialState
  m := program

structure TapeData where
  input : List Token
  first : List Bool
  second : List Bool
  resultReverse : List Bool
  output : List Bool

def tapes (data : TapeData) : ∀ stack, List (Alphabet stack)
  | .input => data.input
  | .first => data.first
  | .second => data.second
  | .resultReverse => data.resultReverse
  | .output => data.output

def cfg (label : Label) (state : State) (data : TapeData) :
    TM2.Cfg Alphabet Label State :=
  ⟨some label, state, tapes data⟩

def scanCfg (data : TapeData) := cfg .scan initialState data

def readFirstCfg (data : TapeData) := cfg .readFirst initialState data

def readSecondCfg (data : TapeData) := cfg .readSecond initialState data

def compareCfg (equal : Bool) (data : TapeData) :=
  cfg .compare ⟨equal, none, none, none⟩ data

def reverseCfg (data : TapeData) := cfg .reverse initialState data

def haltCfg (output : List Bool) : TM2.Cfg Alphabet Label State :=
  ⟨none, initialState, tapes ⟨[], [], [], [], output⟩⟩

def oneStep {first last : TM2.Cfg Alphabet Label State}
    (step : TM2.step program first = some last) :
    EvalsToInTime (TM2.step program) first (some last) 1 :=
  FiniteBlockTransducer.oneStep step

end DelimitedBinaryWordPairEqualityMachine
end LeanTrominoes
