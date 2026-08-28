/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairBooleanFilterData

/-! # Machine filtering delimited binary-word pairs by Boolean controls -/

noncomputable section

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPairBooleanFilterMachine

open DelimitedBinaryWordPairBooleanFilter

abbrev InputToken :=
  DelimitedBinaryWordPairBooleanFilter.InputToken
abbrev PairToken := DelimitedBinaryWordPairs.Token

inductive Stack
  | input
  | controlReverse
  | controls
  | outputReverse
  | output
  deriving DecidableEq, Fintype

inductive Label
  | scanControls
  | restoreControls
  | scanPairs
  | readControl
  | scanPair
  | clearControls
  | reverseOutput
  deriving Fintype

structure State where
  input : Option InputToken
  control : Option Bool
  output : Option PairToken
  deriving DecidableEq, Fintype

def initialState : State := ⟨none, none, none⟩

instance : Inhabited State := ⟨initialState⟩

abbrev Alphabet : Stack → Type
  | .input => InputToken
  | .controlReverse | .controls => Bool
  | .outputReverse | .output => PairToken

def setInput (state : State) (symbol : Option InputToken) : State :=
  { state with input := symbol }

def setControl (state : State) (control : Option Bool) : State :=
  { state with control := control }

def setOutput (state : State) (symbol : Option PairToken) : State :=
  { state with output := symbol }

def clearInput (state : State) : State := { state with input := none }
def clearControl (state : State) : State := { state with control := none }
def clearOutput (state : State) : State := { state with output := none }

def inputIsNone (state : State) : Bool := state.input.isNone

def inputIsLeft : State → Bool
  | ⟨some (.left _), _, _⟩ => true
  | _ => false

def inputIsSeparator : State → Bool
  | ⟨some .separator, _, _⟩ => true
  | _ => false

def inputIsPairStart : State → Bool
  | ⟨some (.right .pairStart), _, _⟩ => true
  | _ => false

def inputIsPairEnd : State → Bool
  | ⟨some (.right .pairEnd), _, _⟩ => true
  | _ => false

def controlIsNone (state : State) : Bool := state.control.isNone
def controlIsActive (state : State) : Bool := state.control.getD false
def outputIsNone (state : State) : Bool := state.output.isNone

def leftControl : State → Bool
  | ⟨some (.left control), _, _⟩ => control
  | _ => false

def rightPairToken : State → PairToken
  | ⟨some (.right token), _, _⟩ => token
  | _ => .pairStart

def controlFromState (state : State) : Bool := state.control.getD false
def outputFromState (state : State) : PairToken :=
  state.output.getD .pairStart

/-- Controls are reversed once into a work stack and restored in forward
order.  Each pair then consumes one control and is copied exactly when that
control is true. -/
def program : Label → TM2.Stmt Alphabet Label State
  | .scanControls =>
      .pop .input setInput
        (.branch inputIsNone
          (.load clearInput (.goto fun _ => .restoreControls))
          (.branch inputIsLeft
            (.push .controlReverse leftControl
              (.load clearInput (.goto fun _ => .scanControls)))
            (.branch inputIsSeparator
              (.load clearInput (.goto fun _ => .restoreControls))
              (.load clearInput (.goto fun _ => .scanControls)))))
  | .restoreControls =>
      .pop .controlReverse setControl
        (.branch controlIsNone
          (.load clearControl (.goto fun _ => .scanPairs))
          (.push .controls controlFromState
            (.load clearControl (.goto fun _ => .restoreControls))))
  | .scanPairs =>
      .pop .input setInput
        (.branch inputIsNone
          (.load clearInput (.goto fun _ => .clearControls))
          (.branch inputIsPairStart
            (.load clearInput (.goto fun _ => .readControl))
            (.load clearInput (.goto fun _ => .scanPairs))))
  | .readControl =>
      .pop .controls setControl
          (.branch controlIsActive
          (.push .outputReverse
            (fun _ => DelimitedBinaryWordPairs.Token.pairStart)
            (.goto fun _ => .scanPair))
          (.goto fun _ => .scanPair))
  | .scanPair =>
      .pop .input setInput
        (.branch inputIsNone
          (.load clearInput (.goto fun _ => .reverseOutput))
          (.branch inputIsPairEnd
            (.branch controlIsActive
              (.push .outputReverse
                (fun _ => DelimitedBinaryWordPairs.Token.pairEnd)
                (.load clearInput
                  (.load clearControl (.goto fun _ => .scanPairs))))
              (.load clearInput
                (.load clearControl (.goto fun _ => .scanPairs))))
            (.branch controlIsActive
              (.push .outputReverse rightPairToken
                (.load clearInput (.goto fun _ => .scanPair)))
              (.load clearInput (.goto fun _ => .scanPair)))))
  | .clearControls =>
      .pop .controls setControl
        (.branch controlIsNone
          (.load clearControl (.goto fun _ => .reverseOutput))
          (.load clearControl (.goto fun _ => .clearControls)))
  | .reverseOutput =>
      .pop .outputReverse setOutput
        (.branch outputIsNone
          (.load clearOutput .halt)
          (.push .output outputFromState
            (.load clearOutput (.goto fun _ => .reverseOutput))))

abbrev machine : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .scanControls
  σ := State
  initialState := initialState
  m := program

end DelimitedBinaryWordPairBooleanFilterMachine
end LeanTrominoes

end
