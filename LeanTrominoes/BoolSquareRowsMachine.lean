/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWords
import LeanTrominoes.FiniteBlockTransducer

/-! # Finite machine delimiting a flat Boolean square into rows -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace BoolSquareRowsMachine

abbrev OutputToken := DelimitedBinaryWords.Token

/-- Delimit a nonempty Boolean word into consecutive rows of the supplied
positive width.  The last row is closed even when it is partial. -/
def rowTokensAux (width : Nat) : Nat → List Bool → List OutputToken
  | _, [] => [.wordEnd]
  | remaining, bit :: bits =>
      .bit bit ::
        if remaining ≤ 1 then
          .wordEnd ::
            if bits.isEmpty then []
            else .wordStart :: rowTokensAux width width bits
        else
          rowTokensAux width (remaining - 1) bits

/-- Interpret a flat Boolean word as rows of width equal to the square root
of its length.  Equality matrices produced upstream always have square
length; the definition remains total on arbitrary words. -/
def rowTokens : List Bool → List OutputToken
  | [] => []
  | bit :: bits =>
      .wordStart ::
        rowTokensAux (Nat.sqrt (bit :: bits).length)
          (Nat.sqrt (bit :: bits).length) (bit :: bits)

inductive Stack
  | input
  | sourceReverse
  | work
  | odd
  | oddRestore
  | root
  | source
  | rowCountdown
  | rowRestore
  | outputReverse
  | output
  deriving DecidableEq, Fintype

inductive Label
  | copyInput
  | initOdd
  | consumeWork
  | consumeOdd
  | checkOdd
  | finishRootStep
  | restoreOdd
  | clearOdd
  | clearOddRestore
  | moveRoot
  | reverseSource
  | startRows
  | emitBit
  | consumeRowCount
  | checkRowCount
  | finishRow
  | restoreRowCount
  | clearRowCountdown
  | clearRowRestore
  | reverseOutput
  deriving Fintype

structure State where
  bit : Option Bool
  present : Bool
  outputToken : Option OutputToken
  deriving DecidableEq, Fintype

def initialState : State := ⟨none, false, none⟩

instance : Inhabited State := ⟨initialState⟩

abbrev Alphabet : Stack → Type
  | .input | .sourceReverse | .source => Bool
  | .work | .odd | .oddRestore | .root |
      .rowCountdown | .rowRestore => Unit
  | .outputReverse | .output => OutputToken

def setBit (state : State) (bit : Option Bool) : State :=
  { state with bit := bit }

def clearBit (state : State) : State :=
  { state with bit := none }

def setPresent (state : State) (unit : Option Unit) : State :=
  { state with present := unit.isSome }

def clearPresent (state : State) : State :=
  { state with present := false }

def setOutputToken (state : State)
    (token : Option OutputToken) : State :=
  { state with outputToken := token }

def clearOutputToken (state : State) : State :=
  { state with outputToken := none }

def bitIsNone (state : State) : Bool := state.bit.isNone

def isPresent (state : State) : Bool := state.present

def outputTokenIsNone (state : State) : Bool :=
  state.outputToken.isNone

def bitFromState (state : State) : Bool :=
  state.bit.getD false

def outputTokenFromState (state : State) : OutputToken :=
  state.outputToken.getD .wordStart

def program : Label → TM2.Stmt Alphabet Label State
  | .copyInput =>
      .pop .input setBit
        (.branch bitIsNone
          (.load clearBit (.goto fun _ => .initOdd))
          (.push .sourceReverse bitFromState
            (.push .work (fun _ => ())
              (.load clearBit (.goto fun _ => .copyInput)))))
  | .initOdd =>
      .push .odd (fun _ => ())
        (.goto fun _ => .consumeWork)
  | .consumeWork =>
      .pop .work setPresent
        (.branch isPresent
          (.load clearPresent (.goto fun _ => .consumeOdd))
          (.load clearPresent (.goto fun _ => .clearOdd)))
  | .consumeOdd =>
      .pop .odd setPresent
        (.branch isPresent
          (.push .oddRestore (fun _ => ())
            (.load clearPresent (.goto fun _ => .checkOdd)))
          (.load clearPresent (.goto fun _ => .clearOdd)))
  | .checkOdd =>
      .peek .odd setPresent
        (.branch isPresent
          (.load clearPresent (.goto fun _ => .consumeWork))
          (.load clearPresent (.goto fun _ => .finishRootStep)))
  | .finishRootStep =>
      .push .root (fun _ => ())
        (.peek .work setPresent
          (.branch isPresent
            (.load clearPresent (.goto fun _ => .restoreOdd))
            (.load clearPresent (.goto fun _ => .clearOdd))))
  | .restoreOdd =>
      .pop .oddRestore setPresent
        (.branch isPresent
          (.push .odd (fun _ => ())
            (.load clearPresent (.goto fun _ => .restoreOdd)))
          (.push .odd (fun _ => ())
            (.push .odd (fun _ => ())
              (.load clearPresent (.goto fun _ => .consumeWork)))))
  | .clearOdd =>
      .pop .odd setPresent
        (.branch isPresent
          (.load clearPresent (.goto fun _ => .clearOdd))
          (.load clearPresent (.goto fun _ => .clearOddRestore)))
  | .clearOddRestore =>
      .pop .oddRestore setPresent
        (.branch isPresent
          (.load clearPresent (.goto fun _ => .clearOddRestore))
          (.load clearPresent (.goto fun _ => .moveRoot)))
  | .moveRoot =>
      .pop .root setPresent
        (.branch isPresent
          (.push .rowCountdown (fun _ => ())
            (.load clearPresent (.goto fun _ => .moveRoot)))
          (.load clearPresent (.goto fun _ => .reverseSource)))
  | .reverseSource =>
      .pop .sourceReverse setBit
        (.branch bitIsNone
          (.load clearBit (.goto fun _ => .startRows))
          (.push .source bitFromState
            (.load clearBit (.goto fun _ => .reverseSource))))
  | .startRows =>
      .peek .source setBit
        (.branch bitIsNone
          (.load clearBit (.goto fun _ => .clearRowCountdown))
          (.push .outputReverse (fun _ => .wordStart)
            (.load clearBit (.goto fun _ => .emitBit))))
  | .emitBit =>
      .pop .source setBit
        (.branch bitIsNone
          (.push .outputReverse (fun _ => .wordEnd)
            (.load clearBit (.goto fun _ => .clearRowCountdown)))
          (.push .outputReverse
            (fun state => .bit (bitFromState state))
            (.load clearBit (.goto fun _ => .consumeRowCount))))
  | .consumeRowCount =>
      .pop .rowCountdown setPresent
        (.branch isPresent
          (.push .rowRestore (fun _ => ())
            (.load clearPresent (.goto fun _ => .checkRowCount)))
          (.push .outputReverse (fun _ => .wordEnd)
            (.load clearPresent (.goto fun _ => .clearRowRestore))))
  | .checkRowCount =>
      .peek .rowCountdown setPresent
        (.branch isPresent
          (.load clearPresent (.goto fun _ => .emitBit))
          (.push .outputReverse (fun _ => .wordEnd)
            (.load clearPresent (.goto fun _ => .finishRow))))
  | .finishRow =>
      .peek .source setBit
        (.branch bitIsNone
          (.load clearBit (.goto fun _ => .clearRowRestore))
          (.load clearBit (.goto fun _ => .restoreRowCount)))
  | .restoreRowCount =>
      .pop .rowRestore setPresent
        (.branch isPresent
          (.push .rowCountdown (fun _ => ())
            (.load clearPresent (.goto fun _ => .restoreRowCount)))
          (.push .outputReverse (fun _ => .wordStart)
            (.load clearPresent (.goto fun _ => .emitBit))))
  | .clearRowCountdown =>
      .pop .rowCountdown setPresent
        (.branch isPresent
          (.load clearPresent (.goto fun _ => .clearRowCountdown))
          (.load clearPresent (.goto fun _ => .clearRowRestore)))
  | .clearRowRestore =>
      .pop .rowRestore setPresent
        (.branch isPresent
          (.load clearPresent (.goto fun _ => .clearRowRestore))
          (.load clearPresent (.goto fun _ => .reverseOutput)))
  | .reverseOutput =>
      .pop .outputReverse setOutputToken
        (.branch outputTokenIsNone
          .halt
          (.push .output outputTokenFromState
            (.load clearOutputToken (.goto fun _ => .reverseOutput))))

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
  input : List Bool
  sourceReverse : List Bool
  work : List Unit
  odd : List Unit
  oddRestore : List Unit
  root : List Unit
  source : List Bool
  rowCountdown : List Unit
  rowRestore : List Unit
  outputReverse : List OutputToken
  output : List OutputToken

def tapes (data : TapeData) : ∀ stack, List (Alphabet stack)
  | .input => data.input
  | .sourceReverse => data.sourceReverse
  | .work => data.work
  | .odd => data.odd
  | .oddRestore => data.oddRestore
  | .root => data.root
  | .source => data.source
  | .rowCountdown => data.rowCountdown
  | .rowRestore => data.rowRestore
  | .outputReverse => data.outputReverse
  | .output => data.output

def cfg (label : Label) (data : TapeData) :
    TM2.Cfg Alphabet Label State :=
  ⟨some label, initialState, tapes data⟩

def copyInputCfg := cfg .copyInput
def initOddCfg := cfg .initOdd
def consumeWorkCfg := cfg .consumeWork
def consumeOddCfg := cfg .consumeOdd
def checkOddCfg := cfg .checkOdd
def finishRootStepCfg := cfg .finishRootStep
def restoreOddCfg := cfg .restoreOdd
def clearOddCfg := cfg .clearOdd
def clearOddRestoreCfg := cfg .clearOddRestore
def moveRootCfg := cfg .moveRoot
def reverseSourceCfg := cfg .reverseSource
def startRowsCfg := cfg .startRows
def emitBitCfg := cfg .emitBit
def consumeRowCountCfg := cfg .consumeRowCount
def checkRowCountCfg := cfg .checkRowCount
def finishRowCfg := cfg .finishRow
def restoreRowCountCfg := cfg .restoreRowCount
def clearRowCountdownCfg := cfg .clearRowCountdown
def clearRowRestoreCfg := cfg .clearRowRestore
def reverseOutputCfg := cfg .reverseOutput

def haltCfg (output : List OutputToken) :
    TM2.Cfg Alphabet Label State :=
  ⟨none, initialState,
    tapes ⟨[], [], [], [], [], [], [], [], [], [], output⟩⟩

def oneStep {first last : TM2.Cfg Alphabet Label State}
    (step : TM2.step program first = some last) :
    EvalsToInTime (TM2.step program) first (some last) 1 :=
  FiniteBlockTransducer.oneStep step

end BoolSquareRowsMachine
end LeanTrominoes
