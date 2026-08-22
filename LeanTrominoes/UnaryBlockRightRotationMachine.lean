/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Complexity
import LeanTrominoes.SeparatedProductEncoding
import LeanTrominoes.UnaryFieldEncoderMachine

/-! # Right rotations of consecutive unary index blocks -/

noncomputable section

namespace LeanTrominoes.UnaryBlockRightRotationMachine

open StateTransition Turing

abbrev UnarySymbol := UnaryFieldEncoderMachine.Symbol
abbrev InputSymbol :=
  SeparatedProductEncoding.Token UnarySymbol UnarySymbol

/-- Right-rotate the consecutive index block beginning at `blockStart`. -/
def rotatedBlock (blockStart : Nat) : Nat → List Nat
  | 0 => []
  | count + 1 =>
      (blockStart + count) ::
        (List.range count).map fun position => blockStart + position

/-- Right-rotate aligned consecutive blocks, truncating if either list ends. -/
def rotatedBlocks : List Nat → List Nat → List Nat
  | groupSize :: groupSizes, blockStart :: blockStarts =>
      rotatedBlock blockStart groupSize ++
        rotatedBlocks groupSizes blockStarts
  | _, _ => []

inductive Stack
  | input
  | sizesReverse
  | sizes
  | startsReverse
  | starts
  | group
  | groupRemaining
  | start
  | startRestore
  | position
  | positionRestore
  | outputReverse
  | output
  deriving DecidableEq, Fintype

inductive Label
  | scanLeft
  | pushSizeReverse
  | scanRight
  | pushStartReverse
  | restoreSizes
  | pushSize
  | restoreStarts
  | pushStart
  | scanSizeField
  | pushGroupUnit
  | scanStartField
  | pushStartUnit
  | beginGroup
  | copyFirstStart
  | restoreFirstStart
  | copyFirstGroup
  | emitFirstDelimiter
  | beginRemaining
  | copyRemainingStart
  | restoreRemainingStart
  | copyPosition
  | restorePosition
  | emitRemainingDelimiter
  | clearStart
  | clearPosition
  | reverseOutput
  | pushOutput
  deriving Fintype

inductive State
  | empty
  | input (symbol : Option InputSymbol)
  | unary (symbol : Option UnarySymbol)
  | unit (symbol : Option Unit)
  deriving Fintype

abbrev Alphabet : Stack → Type
  | .input => InputSymbol
  | .sizesReverse | .sizes | .startsReverse | .starts |
      .outputReverse | .output => UnarySymbol
  | .group | .groupRemaining | .start | .startRestore |
      .position | .positionRestore => Unit

def inputSymbol : State → Option InputSymbol
  | .input symbol => symbol
  | _ => none

def unarySymbol : State → Option UnarySymbol
  | .unary symbol => symbol
  | _ => none

def unitSymbol : State → Option Unit
  | .unit symbol => symbol
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

def unitIsNone (state : State) : Bool := (unitSymbol state).isNone

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
          (.load clear (.goto fun _ => .restoreSizes))
          (.branch inputIsLeft
            (.goto fun _ => .pushSizeReverse)
            (.branch inputIsSeparator
              (.load clear (.goto fun _ => .scanRight))
              (.load clear (.goto fun _ => .scanLeft)))))
  | .pushSizeReverse =>
      .push .sizesReverse leftSymbol
        (.load clear (.goto fun _ => .scanLeft))
  | .scanRight =>
      .pop .input (fun _ symbol => .input symbol)
        (.branch inputIsNone
          (.load clear (.goto fun _ => .restoreSizes))
          (.branch inputIsRight
            (.goto fun _ => .pushStartReverse)
            (.load clear (.goto fun _ => .scanRight))))
  | .pushStartReverse =>
      .push .startsReverse rightSymbol
        (.load clear (.goto fun _ => .scanRight))
  | .restoreSizes =>
      .pop .sizesReverse (fun _ symbol => .unary symbol)
        (.branch unaryIsNone
          (.load clear (.goto fun _ => .restoreStarts))
          (.goto fun _ => .pushSize))
  | .pushSize =>
      .push .sizes storedUnary
        (.load clear (.goto fun _ => .restoreSizes))
  | .restoreStarts =>
      .pop .startsReverse (fun _ symbol => .unary symbol)
        (.branch unaryIsNone
          (.load clear (.goto fun _ => .scanSizeField))
          (.goto fun _ => .pushStart))
  | .pushStart =>
      .push .starts storedUnary
        (.load clear (.goto fun _ => .restoreStarts))
  | .scanSizeField =>
      .pop .sizes (fun _ symbol => .unary symbol)
        (.branch unaryIsNone
          (.load clear (.goto fun _ => .reverseOutput))
          (.branch unaryIsUnit
            (.goto fun _ => .pushGroupUnit)
            (.load clear (.goto fun _ => .scanStartField))))
  | .pushGroupUnit =>
      .push .group (fun _ => ())
        (.load clear (.goto fun _ => .scanSizeField))
  | .scanStartField =>
      .pop .starts (fun _ symbol => .unary symbol)
        (.branch unaryIsNone
          (.load clear (.goto fun _ => .beginGroup))
          (.branch unaryIsUnit
            (.goto fun _ => .pushStartUnit)
            (.load clear (.goto fun _ => .beginGroup))))
  | .pushStartUnit =>
      .push .start (fun _ => ())
        (.load clear (.goto fun _ => .scanStartField))
  | .beginGroup =>
      .pop .group (fun _ symbol => .unit symbol)
        (.branch unitIsNone
          (.load clear (.goto fun _ => .clearStart))
          (.load clear (.goto fun _ => .copyFirstStart)))
  | .copyFirstStart =>
      .pop .start (fun _ symbol => .unit symbol)
        (.branch unitIsNone
          (.load clear (.goto fun _ => .restoreFirstStart))
          (.push .startRestore (fun _ => ())
            (.push .outputReverse (fun _ => .unit)
              (.load clear (.goto fun _ => .copyFirstStart)))))
  | .restoreFirstStart =>
      .pop .startRestore (fun _ symbol => .unit symbol)
        (.branch unitIsNone
          (.load clear (.goto fun _ => .copyFirstGroup))
          (.push .start (fun _ => ())
            (.load clear (.goto fun _ => .restoreFirstStart))))
  | .copyFirstGroup =>
      .pop .group (fun _ symbol => .unit symbol)
        (.branch unitIsNone
          (.load clear (.goto fun _ => .emitFirstDelimiter))
          (.push .groupRemaining (fun _ => ())
            (.push .outputReverse (fun _ => .unit)
              (.load clear (.goto fun _ => .copyFirstGroup)))))
  | .emitFirstDelimiter =>
      .push .outputReverse (fun _ => .delimiter)
        (.goto fun _ => .beginRemaining)
  | .beginRemaining =>
      .pop .groupRemaining (fun _ symbol => .unit symbol)
        (.branch unitIsNone
          (.load clear (.goto fun _ => .clearStart))
          (.load clear (.goto fun _ => .copyRemainingStart)))
  | .copyRemainingStart =>
      .pop .start (fun _ symbol => .unit symbol)
        (.branch unitIsNone
          (.load clear (.goto fun _ => .restoreRemainingStart))
          (.push .startRestore (fun _ => ())
            (.push .outputReverse (fun _ => .unit)
              (.load clear (.goto fun _ => .copyRemainingStart)))))
  | .restoreRemainingStart =>
      .pop .startRestore (fun _ symbol => .unit symbol)
        (.branch unitIsNone
          (.load clear (.goto fun _ => .copyPosition))
          (.push .start (fun _ => ())
            (.load clear (.goto fun _ => .restoreRemainingStart))))
  | .copyPosition =>
      .pop .position (fun _ symbol => .unit symbol)
        (.branch unitIsNone
          (.load clear (.goto fun _ => .restorePosition))
          (.push .positionRestore (fun _ => ())
            (.push .outputReverse (fun _ => .unit)
              (.load clear (.goto fun _ => .copyPosition)))))
  | .restorePosition =>
      .pop .positionRestore (fun _ symbol => .unit symbol)
        (.branch unitIsNone
          (.load clear (.goto fun _ => .emitRemainingDelimiter))
          (.push .position (fun _ => ())
            (.load clear (.goto fun _ => .restorePosition))))
  | .emitRemainingDelimiter =>
      .push .outputReverse (fun _ => .delimiter)
        (.push .position (fun _ => ())
          (.goto fun _ => .beginRemaining))
  | .clearStart =>
      .pop .start (fun _ symbol => .unit symbol)
        (.branch unitIsNone
          (.load clear (.goto fun _ => .clearPosition))
          (.load clear (.goto fun _ => .clearStart)))
  | .clearPosition =>
      .pop .position (fun _ symbol => .unit symbol)
        (.branch unitIsNone
          (.load clear (.goto fun _ => .scanSizeField))
          (.load clear (.goto fun _ => .clearPosition)))
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

end LeanTrominoes.UnaryBlockRightRotationMachine

end
