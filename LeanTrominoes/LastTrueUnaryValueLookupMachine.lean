/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Complexity
import LeanTrominoes.DelimitedBinaryWords
import LeanTrominoes.SeparatedProductEncoding
import LeanTrominoes.UnaryFieldEncoderMachine

/-! # Looking up the unary value at each row's last true position -/

noncomputable section

namespace LeanTrominoes
namespace LastTrueUnaryValueLookupMachine

open StateTransition Turing

abbrev RowSymbol := DelimitedBinaryWords.Token
abbrev UnarySymbol := UnaryFieldEncoderMachine.Symbol
abbrev InputSymbol :=
  SeparatedProductEncoding.Token RowSymbol UnarySymbol

/-- Scan aligned row/value positions, replacing the candidate at every true
bit.  Missing values act like zero, while extra values are ignored. -/
def lookupAux : Nat → List Bool → List Nat → Nat
  | candidate, [], _ => candidate
  | candidate, false :: bits, [] => lookupAux candidate bits []
  | _, true :: bits, [] => lookupAux 0 bits []
  | candidate, false :: bits, _ :: values => lookupAux candidate bits values
  | _, true :: bits, value :: values => lookupAux value bits values

def lookup (row : List Bool) (values : List Nat) : Nat :=
  lookupAux 0 row values

def lookups (rows : List (List Bool)) (values : List Nat) : List Nat :=
  rows.map fun row => lookup row values

inductive Stack
  | input
  | rowsReverse
  | rows
  | valuesReverse
  | values
  | valuesRestore
  | candidate
  | outputReverse
  | output
  deriving DecidableEq, Fintype

inductive Label
  | scanLeft
  | pushRowReverse
  | scanRight
  | pushValueReverse
  | restoreRows
  | pushRow
  | restoreInitialValues
  | pushInitialValue
  | scanRows
  | nextBit
  | prepareValue
  | clearCandidate
  | readValue
  | pushValueRestore
  | pushCandidateUnit
  | drainCandidate
  | pushOutputUnit
  | emitDelimiter
  | restoreValues
  | pushRestoredValue
  | reverseOutput
  | pushOutput
  deriving Fintype

structure State where
  input : Option InputSymbol
  row : Option RowSymbol
  unary : Option UnarySymbol
  candidate : Option Unit
  deriving DecidableEq, Fintype

def initialState : State := ⟨none, none, none, none⟩

instance : Inhabited State := ⟨initialState⟩

abbrev Alphabet : Stack → Type
  | .input => InputSymbol
  | .rowsReverse | .rows => RowSymbol
  | .valuesReverse | .values | .valuesRestore |
      .outputReverse | .output => UnarySymbol
  | .candidate => Unit

def setInput (state : State) (symbol : Option InputSymbol) : State :=
  { state with input := symbol }

def setRow (state : State) (symbol : Option RowSymbol) : State :=
  { state with row := symbol }

def setUnary (state : State) (symbol : Option UnarySymbol) : State :=
  { state with unary := symbol }

def setCandidate (state : State) (symbol : Option Unit) : State :=
  { state with candidate := symbol }

def clearInput (state : State) : State := { state with input := none }
def clearRow (state : State) : State := { state with row := none }
def clearUnary (state : State) : State := { state with unary := none }
def clearCandidateState (state : State) : State :=
  { state with candidate := none }

def inputIsNone (state : State) : Bool := state.input.isNone

def inputIsLeft (state : State) : Bool :=
  match state.input with
  | some (.left _) => true
  | _ => false

def inputIsSeparator (state : State) : Bool :=
  match state.input with
  | some .separator => true
  | _ => false

def inputIsRight (state : State) : Bool :=
  match state.input with
  | some (.right _) => true
  | _ => false

def rowIsNone (state : State) : Bool := state.row.isNone

def rowIsStart (state : State) : Bool :=
  match state.row with
  | some .wordStart => true
  | _ => false

def rowIsBit (state : State) : Bool :=
  match state.row with
  | some (.bit _) => true
  | _ => false

def rowBitIsTrue (state : State) : Bool :=
  match state.row with
  | some (.bit true) => true
  | _ => false

def unaryIsNone (state : State) : Bool := state.unary.isNone

def unaryIsUnit (state : State) : Bool :=
  match state.unary with
  | some .unit => true
  | _ => false

def candidateIsNone (state : State) : Bool := state.candidate.isNone

def leftRow (state : State) : RowSymbol :=
  match state.input with
  | some (.left symbol) => symbol
  | _ => .wordStart

def rightUnary (state : State) : UnarySymbol :=
  match state.input with
  | some (.right symbol) => symbol
  | _ => .delimiter

def storedRow (state : State) : RowSymbol :=
  state.row.getD .wordStart

def storedUnary (state : State) : UnarySymbol :=
  state.unary.getD .delimiter

def program : Label → TM2.Stmt Alphabet Label State
  | .scanLeft =>
      .pop .input setInput
        (.branch inputIsNone
          (.load clearInput (.goto fun _ => .restoreRows))
          (.branch inputIsLeft
            (.goto fun _ => .pushRowReverse)
            (.branch inputIsSeparator
              (.load clearInput (.goto fun _ => .scanRight))
              (.load clearInput (.goto fun _ => .scanLeft)))))
  | .pushRowReverse =>
      .push .rowsReverse leftRow
        (.load clearInput (.goto fun _ => .scanLeft))
  | .scanRight =>
      .pop .input setInput
        (.branch inputIsNone
          (.load clearInput (.goto fun _ => .restoreRows))
          (.branch inputIsRight
            (.goto fun _ => .pushValueReverse)
            (.load clearInput (.goto fun _ => .scanRight))))
  | .pushValueReverse =>
      .push .valuesReverse rightUnary
        (.load clearInput (.goto fun _ => .scanRight))
  | .restoreRows =>
      .pop .rowsReverse setRow
        (.branch rowIsNone
          (.load clearRow (.goto fun _ => .restoreInitialValues))
          (.goto fun _ => .pushRow))
  | .pushRow =>
      .push .rows storedRow
        (.load clearRow (.goto fun _ => .restoreRows))
  | .restoreInitialValues =>
      .pop .valuesReverse setUnary
        (.branch unaryIsNone
          (.load clearUnary (.goto fun _ => .scanRows))
          (.goto fun _ => .pushInitialValue))
  | .pushInitialValue =>
      .push .values storedUnary
        (.load clearUnary (.goto fun _ => .restoreInitialValues))
  | .scanRows =>
      .pop .rows setRow
        (.branch rowIsNone
          (.load clearRow (.goto fun _ => .reverseOutput))
          (.branch rowIsStart
            (.load clearRow (.goto fun _ => .nextBit))
            (.load clearRow (.goto fun _ => .scanRows))))
  | .nextBit =>
      .pop .rows setRow
        (.branch rowIsNone
          (.load clearRow (.goto fun _ => .drainCandidate))
          (.branch rowIsBit
            (.goto fun _ => .prepareValue)
            (.load clearRow (.goto fun _ => .drainCandidate))))
  | .prepareValue =>
      .branch rowBitIsTrue
        (.load clearUnary (.goto fun _ => .clearCandidate))
        (.load clearUnary (.goto fun _ => .readValue))
  | .clearCandidate =>
      .pop .candidate setCandidate
        (.branch candidateIsNone
          (.load clearCandidateState (.goto fun _ => .readValue))
          (.load clearCandidateState (.goto fun _ => .clearCandidate)))
  | .readValue =>
      .pop .values setUnary
        (.branch unaryIsNone
          (.load clearUnary (.goto fun _ => .nextBit))
          (.goto fun _ => .pushValueRestore))
  | .pushValueRestore =>
      .push .valuesRestore storedUnary
        (.branch unaryIsUnit
          (.branch rowBitIsTrue
            (.goto fun _ => .pushCandidateUnit)
            (.load clearUnary (.goto fun _ => .readValue)))
          (.load clearUnary (.goto fun _ => .nextBit)))
  | .pushCandidateUnit =>
      .push .candidate (fun _ => ())
        (.load clearUnary (.goto fun _ => .readValue))
  | .drainCandidate =>
      .pop .candidate setCandidate
        (.branch candidateIsNone
          (.load clearCandidateState (.goto fun _ => .emitDelimiter))
          (.load clearCandidateState (.goto fun _ => .pushOutputUnit)))
  | .pushOutputUnit =>
      .push .outputReverse (fun _ => .unit)
        (.goto fun _ => .drainCandidate)
  | .emitDelimiter =>
      .push .outputReverse (fun _ => .delimiter)
        (.goto fun _ => .restoreValues)
  | .restoreValues =>
      .pop .valuesRestore setUnary
        (.branch unaryIsNone
          (.load clearUnary (.goto fun _ => .scanRows))
          (.goto fun _ => .pushRestoredValue))
  | .pushRestoredValue =>
      .push .values storedUnary
        (.load clearUnary (.goto fun _ => .restoreValues))
  | .reverseOutput =>
      .pop .outputReverse setUnary
        (.branch unaryIsNone
          (.load clearUnary .halt)
          (.goto fun _ => .pushOutput))
  | .pushOutput =>
      .push .output storedUnary
        (.load clearUnary (.goto fun _ => .reverseOutput))

abbrev machine : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .scanLeft
  σ := State
  initialState := initialState
  m := program

end LastTrueUnaryValueLookupMachine
end LeanTrominoes
