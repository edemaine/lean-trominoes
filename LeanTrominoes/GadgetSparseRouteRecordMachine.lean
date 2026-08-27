/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteRecordTokenSemantics

/-! # Finite complement-counter route-record machine

The machine parses one normalized request block, maintains the horizontal
coordinate as two complementary unary counters, and maintains the signed
vertical coordinate as positive/negative unary magnitudes.  Each internal
route cell is copied nondestructively into a canonical sparse assignment
record.  Output is accumulated in reverse and reversed once at the end.
-/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace GadgetSparseRouteRecordMachine

open Gadget
open PeriodicCNFStripReduction

abbrev InputToken := GadgetSparseRouteRecordTokens.InputToken
abbrev OutputToken := GadgetSparseRouteRecordTokens.OutputToken

inductive Stack
  | input
  | horizontal
  | horizontalComplement
  | verticalPositive
  | verticalNegative
  | scratch
  | outputReverse
  | output
  deriving DecidableEq, Fintype

inductive Label
  | scanPeriod
  | scanHorizontal
  | moveHorizontal
  | reserveComplement
  | scanVertical
  | scanColor
  | scanIncoming (color : WireColor)
  | advance (color : WireColor) (incoming : AxisDirection)
  | wrapEast (color : WireColor) (incoming : AxisDirection)
  | wrapWest (color : WireColor) (incoming : AxisDirection)
  | scanOutgoing (color : WireColor) (incoming : AxisDirection)
  | beginRecord (color : WireColor) (incoming outgoing : AxisDirection)
  | copyHorizontal (color : WireColor)
      (incoming outgoing : AxisDirection)
  | restoreHorizontal (color : WireColor)
      (incoming outgoing : AxisDirection)
  | copyVertical (color : WireColor)
      (incoming outgoing : AxisDirection)
  | restoreVertical (color : WireColor)
      (incoming outgoing : AxisDirection)
  | reverseOutput
  deriving Fintype

/-- A transition temporarily retains an input token, unary unit, or output
token. -/
abbrev State := Option (InputToken ⊕ (Unit ⊕ OutputToken))

abbrev Alphabet : Stack → Type
  | .input => InputToken
  | .horizontal | .horizontalComplement
  | .verticalPositive | .verticalNegative | .scratch => Unit
  | .outputReverse | .output => OutputToken

def isInputUnitState : State → Bool
  | some (.inl .unit) => true
  | _ => false

def isPeriodEndState : State → Bool
  | some (.inl .periodEnd) => true
  | _ => false

def isHorizontalEndState : State → Bool
  | some (.inl .horizontalEnd) => true
  | _ => false

def isVerticalEndState : State → Bool
  | some (.inl .verticalEnd) => true
  | _ => false

def isColorState : State → Bool
  | some (.inl (.color _)) => true
  | _ => false

def isDirectionState : State → Bool
  | some (.inl (.direction _)) => true
  | _ => false

def colorFromState : State → WireColor
  | some (.inl (.color color)) => color
  | _ => .red

def directionFromState : State → AxisDirection
  | some (.inl (.direction direction)) => direction
  | _ => .invalid

def outputFromState : State → OutputToken
  | some (.inr (.inr token)) => token
  | _ => default

def loadInput : State → Option InputToken → State :=
  fun _ token => token.map Sum.inl

def loadUnit : State → Option Unit → State :=
  fun _ unit => unit.map fun _ => Sum.inr (Sum.inl ())

def loadOutput : State → Option OutputToken → State :=
  fun _ token => token.map fun value => Sum.inr (Sum.inr value)

def clearGoto (label : Label) : TM2.Stmt Alphabet Label State :=
  .load (fun _ => none) (.goto fun _ => label)

def afterAdvance (color : WireColor) (incoming : AxisDirection) :
    TM2.Stmt Alphabet Label State :=
  clearGoto (.scanOutgoing color incoming)

/-- One-block complement-counter program. -/
def program : Label → TM2.Stmt Alphabet Label State
  | .scanPeriod =>
      .pop .input loadInput
        (.branch Option.isNone
          (.goto fun _ => .reverseOutput)
          (.branch isInputUnitState
            (.push .horizontalComplement (fun _ => ())
              (clearGoto .scanPeriod))
            (.branch isPeriodEndState
              (clearGoto .scanHorizontal)
              (.goto fun _ => .reverseOutput))))
  | .scanHorizontal =>
      .pop .input loadInput
        (.branch Option.isNone
          (.goto fun _ => .reverseOutput)
          (.branch isInputUnitState
            (.goto fun _ => .moveHorizontal)
            (.branch isHorizontalEndState
              (.goto fun _ => .reserveComplement)
              (.goto fun _ => .reverseOutput))))
  | .moveHorizontal =>
      .pop .horizontalComplement loadUnit
        (.branch Option.isNone
          (.goto fun _ => .reverseOutput)
          (.push .horizontal (fun _ => ())
            (clearGoto .scanHorizontal)))
  | .reserveComplement =>
      .pop .horizontalComplement loadUnit
        (.branch Option.isNone
          (.goto fun _ => .reverseOutput)
          (clearGoto .scanVertical))
  | .scanVertical =>
      .pop .input loadInput
        (.branch Option.isNone
          (.goto fun _ => .reverseOutput)
          (.branch isInputUnitState
            (.push .verticalPositive (fun _ => ())
              (clearGoto .scanVertical))
            (.branch isVerticalEndState
              (clearGoto .scanColor)
              (.goto fun _ => .reverseOutput))))
  | .scanColor =>
      .pop .input loadInput
        (.branch isColorState
          (.goto fun state => .scanIncoming (colorFromState state))
          (.goto fun _ => .reverseOutput))
  | .scanIncoming color =>
      .pop .input loadInput
        (.branch isDirectionState
          (.goto fun state => .advance color (directionFromState state))
          (.goto fun _ => .reverseOutput))
  | .advance color incoming =>
      match incoming with
      | .east =>
          .pop .horizontalComplement loadUnit
            (.branch Option.isNone
              (.goto fun _ => .wrapEast color incoming)
              (.push .horizontal (fun _ => ())
                (afterAdvance color incoming)))
      | .west =>
          .pop .horizontal loadUnit
            (.branch Option.isNone
              (.goto fun _ => .wrapWest color incoming)
              (.push .horizontalComplement (fun _ => ())
                (afterAdvance color incoming)))
      | .north =>
          .pop .verticalPositive loadUnit
            (.branch Option.isNone
              (.push .verticalNegative (fun _ => ())
                (afterAdvance color incoming))
              (afterAdvance color incoming))
      | .south =>
          .pop .verticalNegative loadUnit
            (.branch Option.isNone
              (.push .verticalPositive (fun _ => ())
                (afterAdvance color incoming))
              (afterAdvance color incoming))
      | .invalid => afterAdvance color incoming
  | .wrapEast color incoming =>
      .pop .horizontal loadUnit
        (.branch Option.isNone
          (afterAdvance color incoming)
          (.push .horizontalComplement (fun _ => ())
            (clearGoto (.wrapEast color incoming))))
  | .wrapWest color incoming =>
      .pop .horizontalComplement loadUnit
        (.branch Option.isNone
          (afterAdvance color incoming)
          (.push .horizontal (fun _ => ())
            (clearGoto (.wrapWest color incoming))))
  | .scanOutgoing color incoming =>
      .pop .input loadInput
        (.branch isDirectionState
          (.goto fun state =>
            .beginRecord color incoming (directionFromState state))
          (.goto fun _ => .reverseOutput))
  | .beginRecord color incoming outgoing =>
      clearGoto (.copyHorizontal color incoming outgoing)
  | .copyHorizontal color incoming outgoing =>
      .pop .horizontal loadUnit
        (.branch Option.isNone
          (.push .outputReverse (fun _ => .fieldEnd)
            (.goto fun _ => .restoreHorizontal color incoming outgoing))
          (.push .scratch (fun _ => ())
            (.push .outputReverse (fun _ => .coordinateUnit)
              (clearGoto (.copyHorizontal color incoming outgoing)))))
  | .restoreHorizontal color incoming outgoing =>
      .pop .scratch loadUnit
        (.branch Option.isNone
          (.goto fun _ => .copyVertical color incoming outgoing)
          (.push .horizontal (fun _ => ())
            (clearGoto (.restoreHorizontal color incoming outgoing))))
  | .copyVertical color incoming outgoing =>
      .pop .verticalPositive loadUnit
        (.branch Option.isNone
          (.push .outputReverse
            (fun _ => .cellType
              (routingCellTypeFromForwardDirections
                incoming outgoing color))
            (.goto fun _ => .restoreVertical color incoming outgoing))
          (.push .scratch (fun _ => ())
            (.push .outputReverse (fun _ => .coordinateUnit)
              (clearGoto (.copyVertical color incoming outgoing)))))
  | .restoreVertical color incoming outgoing =>
      .pop .scratch loadUnit
        (.branch Option.isNone
          (.goto fun _ => .advance color outgoing)
          (.push .verticalPositive (fun _ => ())
            (clearGoto (.restoreVertical color incoming outgoing))))
  | .reverseOutput =>
      .pop .outputReverse loadOutput
        (.branch Option.isNone
          .halt
          (.push .output outputFromState
            (clearGoto .reverseOutput)))

abbrev machine : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .scanPeriod
  σ := State
  initialState := none
  m := program

structure TapeData where
  input : List InputToken
  horizontal : List Unit
  horizontalComplement : List Unit
  verticalPositive : List Unit
  verticalNegative : List Unit
  scratch : List Unit
  outputReverse : List OutputToken
  output : List OutputToken

def tapes (data : TapeData) : ∀ stack, List (Alphabet stack)
  | .input => data.input
  | .horizontal => data.horizontal
  | .horizontalComplement => data.horizontalComplement
  | .verticalPositive => data.verticalPositive
  | .verticalNegative => data.verticalNegative
  | .scratch => data.scratch
  | .outputReverse => data.outputReverse
  | .output => data.output

def cfg (label : Label) (state : State) (data : TapeData) :
    TM2.Cfg Alphabet Label State :=
  ⟨some label, state, tapes data⟩

def labelCfg (label : Label) (data : TapeData) := cfg label none data

def scanPeriodCfg (data : TapeData) := labelCfg .scanPeriod data
def scanHorizontalCfg (data : TapeData) := labelCfg .scanHorizontal data
def moveHorizontalCfg (state : State) (data : TapeData) :=
  cfg .moveHorizontal state data
def reserveComplementCfg (state : State) (data : TapeData) :=
  cfg .reserveComplement state data
def scanVerticalCfg (data : TapeData) := labelCfg .scanVertical data
def scanColorCfg (data : TapeData) := labelCfg .scanColor data
def scanIncomingCfg (color : WireColor) (data : TapeData) :=
  labelCfg (.scanIncoming color) data
def advanceCfg (color : WireColor) (incoming : AxisDirection)
    (state : State) (data : TapeData) :=
  cfg (.advance color incoming) state data
def wrapEastCfg (color : WireColor) (incoming : AxisDirection)
    (data : TapeData) := labelCfg (.wrapEast color incoming) data
def wrapWestCfg (color : WireColor) (incoming : AxisDirection)
    (data : TapeData) := labelCfg (.wrapWest color incoming) data
def scanOutgoingCfg (color : WireColor) (incoming : AxisDirection)
    (data : TapeData) := labelCfg (.scanOutgoing color incoming) data
def beginRecordCfg (color : WireColor) (incoming outgoing : AxisDirection)
    (state : State) (data : TapeData) :=
  cfg (.beginRecord color incoming outgoing) state data
def copyHorizontalCfg (color : WireColor)
    (incoming outgoing : AxisDirection) (data : TapeData) :=
  labelCfg (.copyHorizontal color incoming outgoing) data
def restoreHorizontalCfg (color : WireColor)
    (incoming outgoing : AxisDirection) (data : TapeData) :=
  labelCfg (.restoreHorizontal color incoming outgoing) data
def copyVerticalCfg (color : WireColor)
    (incoming outgoing : AxisDirection) (data : TapeData) :=
  labelCfg (.copyVertical color incoming outgoing) data
def restoreVerticalCfg (color : WireColor)
    (incoming outgoing : AxisDirection) (data : TapeData) :=
  labelCfg (.restoreVertical color incoming outgoing) data
def reverseOutputCfg (data : TapeData) := labelCfg .reverseOutput data

def haltCfg (data : TapeData) : TM2.Cfg Alphabet Label State :=
  ⟨none, none, tapes data⟩

def initialData (tokens : List InputToken) : TapeData :=
  ⟨tokens, [], [], [], [], [], [], []⟩

def initialCfg (tokens : List InputToken) :
    TM2.Cfg Alphabet Label State :=
  scanPeriodCfg (initialData tokens)

def signedPositive (vertical : Int) : Nat := vertical.toNat

def signedNegative (vertical : Int) : Nat := (-vertical).toNat

/-- Canonical live counters for a semantic complement location. -/
def locationData (input : List InputToken)
    (location : ComplementLocation)
    (outputReverse output : List OutputToken) : TapeData :=
  { input := input
    horizontal := List.replicate location.horizontal ()
    horizontalComplement :=
      List.replicate location.horizontalComplement ()
    verticalPositive := List.replicate (signedPositive location.vertical) ()
    verticalNegative := List.replicate (signedNegative location.vertical) ()
    scratch := []
    outputReverse := outputReverse
    output := output }

end GadgetSparseRouteRecordMachine
end LeanTrominoes
