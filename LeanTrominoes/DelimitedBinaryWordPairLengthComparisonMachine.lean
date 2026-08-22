/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairs
import LeanTrominoes.FiniteBlockTransducer

/-! # Finite machine for comparing delimited binary-word lengths -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPairLengthComparisonMachine

open DelimitedBinaryWordPairs

inductive LengthOrdering
  | less
  | equal
  | greater
  deriving DecidableEq, Fintype, Inhabited

/-- Compare two natural numbers. -/
def compareNats : Nat → Nat → LengthOrdering
  | 0, 0 => .equal
  | _ + 1, 0 => .greater
  | 0, _ + 1 => .less
  | first + 1, second + 1 => compareNats first second

/-- Compare two list lengths without inspecting their elements. -/
def compareLengths (first : List α) (second : List β) : LengthOrdering :=
  compareNats first.length second.length

/-- Preserve an earlier strict result when the remaining suffix lengths are
equal, and otherwise use the strict suffix result. -/
def compareFrom (current : LengthOrdering)
    (first : List α) (second : List β) : LengthOrdering :=
  match compareLengths first second with
  | .equal => current
  | .less => .less
  | .greater => .greater

def lengthOrderings (input : Input) : List LengthOrdering :=
  input.pairs.map fun pair => compareLengths pair.1 pair.2

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
  ordering : LengthOrdering
  token : Option Token
  first : Option Bool
  second : Option Bool
  result : Option LengthOrdering
  deriving DecidableEq, Fintype

def initialState : State := ⟨.equal, none, none, none, none⟩

instance : Inhabited State := ⟨initialState⟩

abbrev Alphabet : Stack → Type
  | .input => Token
  | .first | .second => Bool
  | .resultReverse | .output => LengthOrdering

def setToken (state : State) (token : Option Token) : State :=
  { state with token := token }

def setFirst (state : State) (first : Option Bool) : State :=
  { state with first := first }

def setSecond (state : State) (second : Option Bool) : State :=
  { state with second := second }

def setResult (state : State) (result : Option LengthOrdering) : State :=
  { state with result := result }

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

def tokenBitFromState (state : State) : Bool :=
  match state.token with
  | some (.firstBit bit) | some (.secondBit bit) => bit
  | _ => false

def orderingFromState (state : State) : LengthOrdering := state.ordering

def resultFromState (state : State) : LengthOrdering :=
  state.result.getD .equal

def clearToken (state : State) : State := { state with token := none }

def clearResult (state : State) : State := { state with result := none }

def advanceCompare (state : State) : State :=
  { ordering :=
      match state.first, state.second with
      | some _, none => .greater
      | none, some _ => .less
      | _, _ => state.ordering
    token := none
    first := none
    second := none
    result := none }

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
            (.push .resultReverse orderingFromState
              (.load (fun _ => initialState) (.goto fun _ => .scan)))
            (.load advanceCompare (.goto fun _ => .compare))))
  | .reverse =>
      .pop .resultReverse setResult
        (.branch (fun state => state.result.isNone)
          .halt
          (.push .output resultFromState
            (.load clearResult (.goto fun _ => .reverse))))

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
  resultReverse : List LengthOrdering
  output : List LengthOrdering

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

def compareCfg (ordering : LengthOrdering) (data : TapeData) :=
  cfg .compare ⟨ordering, none, none, none, none⟩ data

def reverseCfg (data : TapeData) := cfg .reverse initialState data

def haltCfg (output : List LengthOrdering) : TM2.Cfg Alphabet Label State :=
  ⟨none, initialState, tapes ⟨[], [], [], [], output⟩⟩

def oneStep {first last : TM2.Cfg Alphabet Label State}
    (step : TM2.step program first = some last) :
    EvalsToInTime (TM2.step program) first (some last) 1 :=
  FiniteBlockTransducer.oneStep step

end DelimitedBinaryWordPairLengthComparisonMachine
end LeanTrominoes
