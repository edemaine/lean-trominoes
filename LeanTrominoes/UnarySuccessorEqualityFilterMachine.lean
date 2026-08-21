/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Complexity
import LeanTrominoes.SeparatedProductEncoding
import LeanTrominoes.UnaryFieldEncoderMachine

/-! # Filtering paired unary fields by successor equality -/

noncomputable section

namespace LeanTrominoes
namespace UnarySuccessorEqualityFilterMachine

open StateTransition Turing

abbrev UnarySymbol := UnaryFieldEncoderMachine.Symbol
abbrev InputSymbol :=
  SeparatedProductEncoding.Token UnarySymbol UnarySymbol

def selectedValue (rank size : Nat) : Nat :=
  if size = rank + 1 then size else 0

def selectedValues (ranks sizes : List Nat) : List Nat :=
  List.zipWith selectedValue ranks sizes

inductive Stack
  | input
  | rankReverse
  | ranks
  | sizeReverse
  | sizes
  | candidate
  | outputReverse
  | output
  deriving DecidableEq, Fintype

inductive Label
  | scanLeft
  | pushRankReverse
  | scanRight
  | pushSizeReverse
  | restoreRanks
  | pushRank
  | restoreSizes
  | pushSize
  | scanRank
  | matchSizeUnit
  | pushMatchedUnit
  | checkExtraSize
  | pushExtraUnit
  | checkSizeDelimiter
  | rejectDrainRank
  | rejectDrainSize
  | clearCandidate
  | drainCandidate
  | pushOutputUnit
  | emitDelimiter
  | reverseOutput
  | pushOutput
  deriving Fintype

inductive State
  | empty
  | input (symbol : Option InputSymbol)
  | unary (symbol : Option UnarySymbol)
  | candidate (symbol : Option Unit)
  deriving Fintype

abbrev Alphabet : Stack → Type
  | .input => InputSymbol
  | .rankReverse | .ranks | .sizeReverse | .sizes |
      .outputReverse | .output => UnarySymbol
  | .candidate => Unit

def inputSymbol : State → Option InputSymbol
  | .input symbol => symbol
  | _ => none

def unarySymbol : State → Option UnarySymbol
  | .unary symbol => symbol
  | _ => none

def inputIsNone : State → Bool := fun state => (inputSymbol state).isNone

def inputIsLeft : State → Bool
  | .input (some (.left _)) => true
  | _ => false

def inputIsSeparator : State → Bool
  | .input (some .separator) => true
  | _ => false

def inputIsRight : State → Bool
  | .input (some (.right _)) => true
  | _ => false

def unaryIsNone : State → Bool := fun state => (unarySymbol state).isNone

def unaryIsUnit : State → Bool
  | .unary (some .unit) => true
  | _ => false

def candidateIsNone : State → Bool
  | .candidate symbol => symbol.isNone
  | _ => true

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
          (.load clear (.goto fun _ => .restoreRanks))
          (.branch inputIsLeft
            (.goto fun _ => .pushRankReverse)
            (.branch inputIsSeparator
              (.load clear (.goto fun _ => .scanRight))
              (.load clear (.goto fun _ => .scanLeft)))))
  | .pushRankReverse =>
      .push .rankReverse leftSymbol
        (.load clear (.goto fun _ => .scanLeft))
  | .scanRight =>
      .pop .input (fun _ symbol => .input symbol)
        (.branch inputIsNone
          (.load clear (.goto fun _ => .restoreRanks))
          (.branch inputIsRight
            (.goto fun _ => .pushSizeReverse)
            (.load clear (.goto fun _ => .scanRight))))
  | .pushSizeReverse =>
      .push .sizeReverse rightSymbol
        (.load clear (.goto fun _ => .scanRight))
  | .restoreRanks =>
      .pop .rankReverse (fun _ symbol => .unary symbol)
        (.branch unaryIsNone
          (.load clear (.goto fun _ => .restoreSizes))
          (.goto fun _ => .pushRank))
  | .pushRank =>
      .push .ranks storedUnary
        (.load clear (.goto fun _ => .restoreRanks))
  | .restoreSizes =>
      .pop .sizeReverse (fun _ symbol => .unary symbol)
        (.branch unaryIsNone
          (.load clear (.goto fun _ => .scanRank))
          (.goto fun _ => .pushSize))
  | .pushSize =>
      .push .sizes storedUnary
        (.load clear (.goto fun _ => .restoreSizes))
  | .scanRank =>
      .pop .ranks (fun _ symbol => .unary symbol)
        (.branch unaryIsNone
          (.load clear (.goto fun _ => .reverseOutput))
          (.branch unaryIsUnit
            (.load clear (.goto fun _ => .matchSizeUnit))
            (.load clear (.goto fun _ => .checkExtraSize))))
  | .matchSizeUnit =>
      .pop .sizes (fun _ symbol => .unary symbol)
        (.branch unaryIsUnit
          (.load clear (.goto fun _ => .pushMatchedUnit))
          (.load clear (.goto fun _ => .rejectDrainRank)))
  | .pushMatchedUnit =>
      .push .candidate (fun _ => ()) (.goto fun _ => .scanRank)
  | .checkExtraSize =>
      .pop .sizes (fun _ symbol => .unary symbol)
        (.branch unaryIsUnit
          (.load clear (.goto fun _ => .pushExtraUnit))
          (.load clear (.goto fun _ => .clearCandidate)))
  | .pushExtraUnit =>
      .push .candidate (fun _ => ()) (.goto fun _ => .checkSizeDelimiter)
  | .checkSizeDelimiter =>
      .pop .sizes (fun _ symbol => .unary symbol)
        (.branch unaryIsNone
          (.load clear (.goto fun _ => .clearCandidate))
          (.branch unaryIsUnit
            (.load clear (.goto fun _ => .rejectDrainSize))
            (.load clear (.goto fun _ => .drainCandidate))))
  | .rejectDrainRank =>
      .pop .ranks (fun _ symbol => .unary symbol)
        (.branch unaryIsNone
          (.load clear (.goto fun _ => .rejectDrainSize))
          (.branch unaryIsUnit
            (.load clear (.goto fun _ => .rejectDrainRank))
            (.load clear (.goto fun _ => .rejectDrainSize))))
  | .rejectDrainSize =>
      .pop .sizes (fun _ symbol => .unary symbol)
        (.branch unaryIsNone
          (.load clear (.goto fun _ => .clearCandidate))
          (.branch unaryIsUnit
            (.load clear (.goto fun _ => .rejectDrainSize))
            (.load clear (.goto fun _ => .clearCandidate))))
  | .clearCandidate =>
      .pop .candidate (fun _ symbol => .candidate symbol)
        (.branch candidateIsNone
          (.load clear (.goto fun _ => .emitDelimiter))
          (.load clear (.goto fun _ => .clearCandidate)))
  | .drainCandidate =>
      .pop .candidate (fun _ symbol => .candidate symbol)
        (.branch candidateIsNone
          (.load clear (.goto fun _ => .emitDelimiter))
          (.load clear (.goto fun _ => .pushOutputUnit)))
  | .pushOutputUnit =>
      .push .outputReverse (fun _ => .unit)
        (.load clear (.goto fun _ => .drainCandidate))
  | .emitDelimiter =>
      .push .outputReverse (fun _ => .delimiter)
        (.load clear (.goto fun _ => .scanRank))
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

end UnarySuccessorEqualityFilterMachine
end LeanTrominoes
