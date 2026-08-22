/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Complexity
import LeanTrominoes.SeparatedProductEncoding
import LeanTrominoes.UnaryFieldEncoderMachine

/-! # Pointwise addition of aligned unary fields -/

noncomputable section

namespace LeanTrominoes
namespace UnaryAlignedAddMachine

open StateTransition Turing

abbrev UnarySymbol := UnaryFieldEncoderMachine.Symbol
abbrev InputSymbol :=
  SeparatedProductEncoding.Token UnarySymbol UnarySymbol

/-- Pointwise sums, truncated when either input list ends. -/
def sums : List Nat → List Nat → List Nat
  | first :: firsts, second :: seconds =>
      (first + second) :: sums firsts seconds
  | _, _ => []

inductive Stack
  | input
  | firstReverse
  | firsts
  | secondReverse
  | seconds
  | outputReverse
  | output
  deriving DecidableEq, Fintype

inductive Label
  | scanLeft
  | pushFirstReverse
  | scanRight
  | pushSecondReverse
  | restoreFirsts
  | pushFirst
  | restoreSeconds
  | pushSecond
  | scanFirstField
  | pushFirstUnit
  | scanSecondField
  | pushSecondUnit
  | emitDelimiter
  | reverseOutput
  | pushOutput
  deriving Fintype

inductive State
  | empty
  | input (symbol : Option InputSymbol)
  | unary (symbol : Option UnarySymbol)
  deriving Fintype

abbrev Alphabet : Stack → Type
  | .input => InputSymbol
  | .firstReverse | .firsts | .secondReverse | .seconds |
      .outputReverse | .output => UnarySymbol

def inputSymbol : State → Option InputSymbol
  | .input symbol => symbol
  | _ => none

def unarySymbol : State → Option UnarySymbol
  | .unary symbol => symbol
  | _ => none

def inputIsNone (state : State) : Bool := (inputSymbol state).isNone

def inputIsLeft : State → Bool
  | .input (some (.left _)) => true
  | _ => false

def inputIsSeparator : State → Bool
  | .input (some .separator) => true
  | _ => false

def inputIsRight : State → Bool
  | .input (some (.right _)) => true
  | _ => false

def unaryIsNone (state : State) : Bool := (unarySymbol state).isNone

def unaryIsUnit : State → Bool
  | .unary (some .unit) => true
  | _ => false

def leftSymbol : State → UnarySymbol
  | .input (some (.left symbol)) => symbol
  | _ => .delimiter

def rightSymbol : State → UnarySymbol
  | .input (some (.right symbol)) => symbol
  | _ => .delimiter

def storedUnary : State → UnarySymbol
  | .unary (some symbol) => symbol
  | _ => .delimiter

def clear : State → State := fun _ => .empty

def program : Label → TM2.Stmt Alphabet Label State
  | .scanLeft =>
      .pop .input (fun _ symbol => .input symbol)
        (.branch inputIsNone
          (.load clear (.goto fun _ => .restoreFirsts))
          (.branch inputIsLeft
            (.goto fun _ => .pushFirstReverse)
            (.branch inputIsSeparator
              (.load clear (.goto fun _ => .scanRight))
              (.load clear (.goto fun _ => .scanLeft)))))
  | .pushFirstReverse =>
      .push .firstReverse leftSymbol
        (.load clear (.goto fun _ => .scanLeft))
  | .scanRight =>
      .pop .input (fun _ symbol => .input symbol)
        (.branch inputIsNone
          (.load clear (.goto fun _ => .restoreFirsts))
          (.branch inputIsRight
            (.goto fun _ => .pushSecondReverse)
            (.load clear (.goto fun _ => .scanRight))))
  | .pushSecondReverse =>
      .push .secondReverse rightSymbol
        (.load clear (.goto fun _ => .scanRight))
  | .restoreFirsts =>
      .pop .firstReverse (fun _ symbol => .unary symbol)
        (.branch unaryIsNone
          (.load clear (.goto fun _ => .restoreSeconds))
          (.goto fun _ => .pushFirst))
  | .pushFirst =>
      .push .firsts storedUnary
        (.load clear (.goto fun _ => .restoreFirsts))
  | .restoreSeconds =>
      .pop .secondReverse (fun _ symbol => .unary symbol)
        (.branch unaryIsNone
          (.load clear (.goto fun _ => .scanFirstField))
          (.goto fun _ => .pushSecond))
  | .pushSecond =>
      .push .seconds storedUnary
        (.load clear (.goto fun _ => .restoreSeconds))
  | .scanFirstField =>
      .pop .firsts (fun _ symbol => .unary symbol)
        (.branch unaryIsNone
          (.load clear (.goto fun _ => .reverseOutput))
          (.branch unaryIsUnit
            (.load clear (.goto fun _ => .pushFirstUnit))
            (.load clear (.goto fun _ => .scanSecondField))))
  | .pushFirstUnit =>
      .push .outputReverse (fun _ => .unit)
        (.goto fun _ => .scanFirstField)
  | .scanSecondField =>
      .pop .seconds (fun _ symbol => .unary symbol)
        (.branch unaryIsNone
          (.load clear (.goto fun _ => .emitDelimiter))
          (.branch unaryIsUnit
            (.load clear (.goto fun _ => .pushSecondUnit))
            (.load clear (.goto fun _ => .emitDelimiter))))
  | .pushSecondUnit =>
      .push .outputReverse (fun _ => .unit)
        (.goto fun _ => .scanSecondField)
  | .emitDelimiter =>
      .push .outputReverse (fun _ => .delimiter)
        (.goto fun _ => .scanFirstField)
  | .reverseOutput =>
      .pop .outputReverse (fun _ symbol => .unary symbol)
        (.branch unaryIsNone
          (.load clear .halt)
          (.goto fun _ => .pushOutput))
  | .pushOutput =>
      .push .output storedUnary
        (.load clear (.goto fun _ => .reverseOutput))

abbrev machine : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .scanLeft
  σ := State
  initialState := .empty
  m := program

end UnaryAlignedAddMachine
end LeanTrominoes
