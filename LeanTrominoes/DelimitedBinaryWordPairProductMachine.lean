/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWords
import LeanTrominoes.DelimitedBinaryWordPairs
import LeanTrominoes.FiniteBlockTransducer

/-! # Finite machine for the ordered product of binary words -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPairProductMachine

abbrev WordToken := DelimitedBinaryWords.Token
abbrev PairToken := DelimitedBinaryWordPairs.Token

/-- Row-major semantic square of a delimited binary-word list. -/
def pairs (input : DelimitedBinaryWords.Input) :
    DelimitedBinaryWordPairs.Input :=
  ⟨input.words.flatMap fun first =>
    input.words.map fun second => (first, second)⟩

inductive Stack
  | input
  | reverse
  | outer
  | source
  | first
  | firstOriginal
  | sourceRestore
  | outputReverse
  | output
  deriving DecidableEq, Fintype

inductive Label
  | copyInput
  | duplicate
  | scanOuter
  | readOuter
  | reverseFirst
  | scanInner
  | emitFirst
  | scanSecond
  | restoreFirst
  | restoreSource
  | clearFirst
  | clearSource
  | reverseOutput
  deriving Fintype

structure State where
  wordToken : Option WordToken
  bit : Option Bool
  pairToken : Option PairToken
  deriving DecidableEq, Fintype

def initialState : State := ⟨none, none, none⟩

instance : Inhabited State := ⟨initialState⟩

abbrev Alphabet : Stack → Type
  | .input | .reverse | .outer | .source | .sourceRestore => WordToken
  | .first | .firstOriginal => Bool
  | .outputReverse | .output => PairToken

def setWordToken (state : State) (token : Option WordToken) : State :=
  { state with wordToken := token }

def setBit (state : State) (bit : Option Bool) : State :=
  { state with bit := bit }

def setPairToken (state : State) (token : Option PairToken) : State :=
  { state with pairToken := token }

def clearWordToken (state : State) : State :=
  { state with wordToken := none }

def clearBit (state : State) : State :=
  { state with bit := none }

def clearPairToken (state : State) : State :=
  { state with pairToken := none }

def wordTokenIsNone (state : State) : Bool := state.wordToken.isNone

def wordTokenIsBit (state : State) : Bool :=
  match state.wordToken with
  | some (.bit _) => true
  | _ => false

def bitIsNone (state : State) : Bool := state.bit.isNone

def wordTokenFromState (state : State) : WordToken :=
  state.wordToken.getD .wordStart

def bitFromState (state : State) : Bool := state.bit.getD false

def wordBitFromState (state : State) : Bool :=
  match state.wordToken with
  | some (.bit bit) => bit
  | _ => false

def pairTokenFromState (state : State) : PairToken :=
  state.pairToken.getD .pairStart

def firstBitTokenFromState (state : State) : PairToken :=
  .firstBit (bitFromState state)

def secondBitTokenFromState (state : State) : PairToken :=
  .secondBit (wordBitFromState state)

def program : Label → TM2.Stmt Alphabet Label State
  | .copyInput =>
      .pop .input setWordToken
        (.branch wordTokenIsNone
          (.load clearWordToken (.goto fun _ => .duplicate))
          (.push .reverse wordTokenFromState
            (.load clearWordToken (.goto fun _ => .copyInput))))
  | .duplicate =>
      .pop .reverse setWordToken
        (.branch wordTokenIsNone
          (.load clearWordToken (.goto fun _ => .scanOuter))
          (.push .outer wordTokenFromState
            (.push .source wordTokenFromState
              (.load clearWordToken (.goto fun _ => .duplicate)))))
  | .scanOuter =>
      .pop .outer setWordToken
        (.branch wordTokenIsNone
          (.load clearWordToken (.goto fun _ => .clearSource))
          (.load clearWordToken (.goto fun _ => .readOuter)))
  | .readOuter =>
      .pop .outer setWordToken
        (.branch wordTokenIsBit
          (.push .first wordBitFromState
            (.load clearWordToken (.goto fun _ => .readOuter)))
          (.load clearWordToken (.goto fun _ => .reverseFirst)))
  | .reverseFirst =>
      .pop .first setBit
        (.branch bitIsNone
          (.load clearBit (.goto fun _ => .scanInner))
          (.push .firstOriginal bitFromState
            (.load clearBit (.goto fun _ => .reverseFirst))))
  | .scanInner =>
      .pop .source setWordToken
        (.branch wordTokenIsNone
          (.load clearWordToken (.goto fun _ => .restoreSource))
          (.push .sourceRestore wordTokenFromState
            (.push .outputReverse
              (fun _ => DelimitedBinaryWordPairs.Token.pairStart)
              (.load clearWordToken (.goto fun _ => .emitFirst)))))
  | .emitFirst =>
      .pop .firstOriginal setBit
        (.branch bitIsNone
          (.push .outputReverse
            (fun _ => DelimitedBinaryWordPairs.Token.middle)
            (.load clearBit (.goto fun _ => .scanSecond)))
          (.push .outputReverse firstBitTokenFromState
            (.push .first bitFromState
              (.load clearBit (.goto fun _ => .emitFirst)))))
  | .scanSecond =>
      .pop .source setWordToken
        (.push .sourceRestore wordTokenFromState
          (.branch wordTokenIsBit
            (.push .outputReverse secondBitTokenFromState
              (.load clearWordToken (.goto fun _ => .scanSecond)))
            (.push .outputReverse
              (fun _ => DelimitedBinaryWordPairs.Token.pairEnd)
              (.load clearWordToken (.goto fun _ => .restoreFirst)))))
  | .restoreFirst =>
      .pop .first setBit
        (.branch bitIsNone
          (.load clearBit (.goto fun _ => .scanInner))
          (.push .firstOriginal bitFromState
            (.load clearBit (.goto fun _ => .restoreFirst))))
  | .restoreSource =>
      .pop .sourceRestore setWordToken
        (.branch wordTokenIsNone
          (.load clearWordToken (.goto fun _ => .clearFirst))
          (.push .source wordTokenFromState
            (.load clearWordToken (.goto fun _ => .restoreSource))))
  | .clearFirst =>
      .pop .firstOriginal setBit
        (.branch bitIsNone
          (.load clearBit (.goto fun _ => .scanOuter))
          (.load clearBit (.goto fun _ => .clearFirst)))
  | .clearSource =>
      .pop .source setWordToken
        (.branch wordTokenIsNone
          (.load clearWordToken (.goto fun _ => .reverseOutput))
          (.load clearWordToken (.goto fun _ => .clearSource)))
  | .reverseOutput =>
      .pop .outputReverse setPairToken
        (.branch (fun state => state.pairToken.isNone)
          .halt
          (.push .output pairTokenFromState
            (.load clearPairToken (.goto fun _ => .reverseOutput))))

abbrev machine : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .copyInput
  σ := State
  initialState := initialState
  m := program

structure TapeData where
  input : List WordToken
  reverse : List WordToken
  outer : List WordToken
  source : List WordToken
  first : List Bool
  firstOriginal : List Bool
  sourceRestore : List WordToken
  outputReverse : List PairToken
  output : List PairToken

def tapes (data : TapeData) : ∀ stack, List (Alphabet stack)
  | .input => data.input
  | .reverse => data.reverse
  | .outer => data.outer
  | .source => data.source
  | .first => data.first
  | .firstOriginal => data.firstOriginal
  | .sourceRestore => data.sourceRestore
  | .outputReverse => data.outputReverse
  | .output => data.output

def cfg (label : Label) (data : TapeData) :
    TM2.Cfg Alphabet Label State :=
  ⟨some label, initialState, tapes data⟩

def copyInputCfg := cfg .copyInput
def duplicateCfg := cfg .duplicate
def scanOuterCfg := cfg .scanOuter
def readOuterCfg := cfg .readOuter
def reverseFirstCfg := cfg .reverseFirst
def scanInnerCfg := cfg .scanInner
def emitFirstCfg := cfg .emitFirst
def scanSecondCfg := cfg .scanSecond
def restoreFirstCfg := cfg .restoreFirst
def restoreSourceCfg := cfg .restoreSource
def clearFirstCfg := cfg .clearFirst
def clearSourceCfg := cfg .clearSource
def reverseOutputCfg := cfg .reverseOutput

def haltCfg (output : List PairToken) : TM2.Cfg Alphabet Label State :=
  ⟨none, initialState,
    tapes ⟨[], [], [], [], [], [], [], [], output⟩⟩

def oneStep {first last : TM2.Cfg Alphabet Label State}
    (step : TM2.step program first = some last) :
    EvalsToInTime (TM2.step program) first (some last) 1 :=
  FiniteBlockTransducer.oneStep step

end DelimitedBinaryWordPairProductMachine
end LeanTrominoes
