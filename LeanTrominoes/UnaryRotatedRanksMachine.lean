/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Complexity
import LeanTrominoes.SeparatedProductEncoding
import LeanTrominoes.UnaryFieldEncoderMachine

/-! # Rotating aligned unary ranks within their groups -/

noncomputable section

namespace LeanTrominoes
namespace UnaryRotatedRanksMachine

open StateTransition Turing

abbrev UnarySymbol := UnaryFieldEncoderMachine.Symbol
abbrev InputSymbol :=
  SeparatedProductEncoding.Token UnarySymbol UnarySymbol

/-- Move zero to the end of a positive-size group and shift every other rank
one position toward zero. -/
def rotatedRank (rank size : Nat) : Nat :=
  if rank = 0 then size - 1 else rank - 1

def rotatedRanks : List Nat → List Nat → List Nat
  | [], _ => []
  | rank :: ranks, [] =>
      rotatedRank rank 0 :: rotatedRanks ranks []
  | rank :: ranks, size :: sizes =>
      rotatedRank rank size :: rotatedRanks ranks sizes

inductive Stack
  | input
  | rankReverse
  | ranks
  | sizeReverse
  | sizes
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
  | positiveRankRest
  | pushPositiveUnit
  | zeroRankFirstSize
  | zeroRankRestSize
  | pushZeroUnit
  | drainSize
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
  | .rankReverse | .ranks | .sizeReverse | .sizes |
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
            (.load clear (.goto fun _ => .positiveRankRest))
            (.load clear (.goto fun _ => .zeroRankFirstSize))))
  | .positiveRankRest =>
      .pop .ranks (fun _ symbol => .unary symbol)
        (.branch unaryIsNone
          (.load clear (.goto fun _ => .drainSize))
          (.branch unaryIsUnit
            (.load clear (.goto fun _ => .pushPositiveUnit))
            (.load clear (.goto fun _ => .drainSize))))
  | .pushPositiveUnit =>
      .push .outputReverse (fun _ => .unit)
        (.goto fun _ => .positiveRankRest)
  | .zeroRankFirstSize =>
      .pop .sizes (fun _ symbol => .unary symbol)
        (.branch unaryIsNone
          (.load clear (.goto fun _ => .emitDelimiter))
          (.branch unaryIsUnit
            (.load clear (.goto fun _ => .zeroRankRestSize))
            (.load clear (.goto fun _ => .emitDelimiter))))
  | .zeroRankRestSize =>
      .pop .sizes (fun _ symbol => .unary symbol)
        (.branch unaryIsNone
          (.load clear (.goto fun _ => .emitDelimiter))
          (.branch unaryIsUnit
            (.load clear (.goto fun _ => .pushZeroUnit))
            (.load clear (.goto fun _ => .emitDelimiter))))
  | .pushZeroUnit =>
      .push .outputReverse (fun _ => .unit)
        (.goto fun _ => .zeroRankRestSize)
  | .drainSize =>
      .pop .sizes (fun _ symbol => .unary symbol)
        (.branch unaryIsNone
          (.load clear (.goto fun _ => .emitDelimiter))
          (.branch unaryIsUnit
            (.load clear (.goto fun _ => .drainSize))
            (.load clear (.goto fun _ => .emitDelimiter))))
  | .emitDelimiter =>
      .push .outputReverse (fun _ => .delimiter)
        (.goto fun _ => .scanRank)
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

end UnaryRotatedRanksMachine
end LeanTrominoes
