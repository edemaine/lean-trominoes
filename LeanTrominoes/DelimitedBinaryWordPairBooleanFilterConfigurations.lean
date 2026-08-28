/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairBooleanFilterMachine

/-! # Configurations of Boolean filtering for binary-word pairs -/

noncomputable section

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPairBooleanFilterMachine

def tapes
    (input : List InputToken)
    (controlReverse controls : List Bool)
    (outputReverse output : List PairToken) :
    ∀ stack, List (Alphabet stack)
  | .input => input
  | .controlReverse => controlReverse
  | .controls => controls
  | .outputReverse => outputReverse
  | .output => output

def scanControlsCfg
    (input : List InputToken) (controlReverse : List Bool) :
    TM2.Cfg Alphabet Label State :=
  ⟨some .scanControls, initialState,
    tapes input controlReverse [] [] []⟩

def restoreControlsCfg
    (input : List InputToken) (controlReverse controls : List Bool) :
    TM2.Cfg Alphabet Label State :=
  ⟨some .restoreControls, initialState,
    tapes input controlReverse controls [] []⟩

def scanPairsCfg
    (input : List InputToken) (controls : List Bool)
    (outputReverse : List PairToken) :
    TM2.Cfg Alphabet Label State :=
  ⟨some .scanPairs, initialState,
    tapes input [] controls outputReverse []⟩

def readControlCfg
    (input : List InputToken) (controls : List Bool)
    (outputReverse : List PairToken) :
    TM2.Cfg Alphabet Label State :=
  ⟨some .readControl, initialState,
    tapes input [] controls outputReverse []⟩

def scanPairCfg
    (input : List InputToken) (controls : List Bool)
    (active : Option Bool) (outputReverse : List PairToken) :
    TM2.Cfg Alphabet Label State :=
  ⟨some .scanPair, ⟨none, active, none⟩,
    tapes input [] controls outputReverse []⟩

def clearControlsCfg
    (controls : List Bool) (outputReverse : List PairToken) :
    TM2.Cfg Alphabet Label State :=
  ⟨some .clearControls, initialState,
    tapes [] [] controls outputReverse []⟩

def reverseOutputCfg
    (outputReverse output : List PairToken) :
    TM2.Cfg Alphabet Label State :=
  ⟨some .reverseOutput, initialState,
    tapes [] [] [] outputReverse output⟩

def haltCfg (output : List PairToken) :
    TM2.Cfg Alphabet Label State :=
  ⟨none, initialState, tapes [] [] [] [] output⟩

theorem step_scanControls_left
    (control : Bool) (input : List InputToken)
    (controlReverse : List Bool) :
    TM2.step program
        (scanControlsCfg (.left control :: input) controlReverse) =
      some (scanControlsCfg input (control :: controlReverse)) := by
  simp [TM2.step, program, scanControlsCfg, tapes, initialState,
    setInput, clearInput, inputIsNone, inputIsLeft, leftControl]
  funext stack
  cases stack <;> simp [tapes, Function.update]

theorem step_scanControls_separator
    (input : List InputToken) (controlReverse : List Bool) :
    TM2.step program
        (scanControlsCfg (.separator :: input) controlReverse) =
      some (restoreControlsCfg input controlReverse []) := by
  simp [TM2.step, program, scanControlsCfg, restoreControlsCfg, tapes,
    initialState, setInput, clearInput, inputIsNone, inputIsLeft,
    inputIsSeparator]
  funext stack
  cases stack <;> simp [tapes, Function.update]

theorem step_restoreControls_cons
    (input : List InputToken) (control : Bool)
    (controlReverse controls : List Bool) :
    TM2.step program
        (restoreControlsCfg input (control :: controlReverse) controls) =
      some (restoreControlsCfg input controlReverse
        (control :: controls)) := by
  simp [TM2.step, program, restoreControlsCfg, tapes, initialState,
    setControl, clearControl, controlIsNone, controlFromState]
  funext stack
  cases stack <;> simp [tapes, Function.update]

theorem step_restoreControls_nil
    (input : List InputToken) (controls : List Bool) :
    TM2.step program (restoreControlsCfg input [] controls) =
      some (scanPairsCfg input controls []) := by
  simp [TM2.step, program, restoreControlsCfg, scanPairsCfg, tapes,
    initialState, setControl, clearControl, controlIsNone]

theorem step_scanPairs_start
    (input : List InputToken) (controls : List Bool)
    (outputReverse : List PairToken) :
    TM2.step program
        (scanPairsCfg (.right .pairStart :: input)
          controls outputReverse) =
      some (readControlCfg input controls outputReverse) := by
  simp [TM2.step, program, scanPairsCfg, readControlCfg, tapes,
    initialState, setInput, clearInput, inputIsNone, inputIsPairStart]
  funext stack
  cases stack <;> simp [tapes, Function.update]

theorem step_scanPairs_nil
    (controls : List Bool) (outputReverse : List PairToken) :
    TM2.step program (scanPairsCfg [] controls outputReverse) =
      some (clearControlsCfg controls outputReverse) := by
  simp [TM2.step, program, scanPairsCfg, clearControlsCfg, tapes,
    initialState, setInput, clearInput, inputIsNone]

theorem step_readControl_cons
    (input : List InputToken) (active : Bool) (controls : List Bool)
    (outputReverse : List PairToken) :
    TM2.step program
        (readControlCfg input (active :: controls) outputReverse) =
      some (scanPairCfg input controls (some active)
        (if active then .pairStart :: outputReverse
          else outputReverse)) := by
  cases active <;>
    simp [TM2.step, program, readControlCfg, scanPairCfg, tapes,
      initialState, setControl, controlIsActive]
  all_goals
    funext stack
    cases stack <;> simp [tapes, Function.update]

theorem step_readControl_nil
    (input : List InputToken) (outputReverse : List PairToken) :
    TM2.step program (readControlCfg input [] outputReverse) =
      some (scanPairCfg input [] none outputReverse) := by
  simp [TM2.step, program, readControlCfg, scanPairCfg, tapes,
    initialState, setControl, controlIsActive]

theorem step_scanPair_token
    (input : List InputToken) (controls : List Bool)
    (active : Option Bool) (token : PairToken)
    (notEnd : token ≠ .pairEnd)
    (outputReverse : List PairToken) :
    TM2.step program
        (scanPairCfg (.right token :: input) controls active outputReverse) =
      some (scanPairCfg input controls active
        (if active.getD false then token :: outputReverse
          else outputReverse)) := by
  rcases active with _ | active
  · cases token <;>
      simp_all [TM2.step, program, scanPairCfg, tapes, setInput,
        clearInput, inputIsNone, inputIsPairEnd, controlIsActive,
        rightPairToken]
    all_goals
      funext stack
      cases stack <;> simp [tapes, Function.update]
  · cases active <;> cases token <;>
      simp_all [TM2.step, program, scanPairCfg, tapes, setInput,
        clearInput, inputIsNone, inputIsPairEnd, controlIsActive,
        rightPairToken]
    all_goals
      funext stack
      cases stack <;> simp [tapes, Function.update]

theorem step_scanPair_end
    (input : List InputToken) (controls : List Bool)
    (active : Option Bool) (outputReverse : List PairToken) :
    TM2.step program
        (scanPairCfg (.right .pairEnd :: input)
          controls active outputReverse) =
      some (scanPairsCfg input controls
        (if active.getD false then .pairEnd :: outputReverse
          else outputReverse)) := by
  rcases active with _ | active
  · simp [TM2.step, program, scanPairCfg, scanPairsCfg, tapes,
      initialState, setInput, clearInput, clearControl,
      inputIsNone, inputIsPairEnd, controlIsActive]
    funext stack
    cases stack <;> simp [tapes, Function.update]
  · cases active <;>
      simp [TM2.step, program, scanPairCfg, scanPairsCfg, tapes,
        initialState, setInput, clearInput, clearControl,
        inputIsNone, inputIsPairEnd, controlIsActive]
    all_goals
      funext stack
      cases stack <;> simp [tapes, Function.update]

theorem step_clearControls_cons
    (control : Bool) (controls : List Bool)
    (outputReverse : List PairToken) :
    TM2.step program
        (clearControlsCfg (control :: controls) outputReverse) =
      some (clearControlsCfg controls outputReverse) := by
  cases control <;>
    simp [TM2.step, program, clearControlsCfg, tapes, initialState,
      setControl, clearControl, controlIsNone]
  all_goals
    funext stack
    cases stack <;> simp [tapes, Function.update]

theorem step_clearControls_nil (outputReverse : List PairToken) :
    TM2.step program (clearControlsCfg [] outputReverse) =
      some (reverseOutputCfg outputReverse []) := by
  simp [TM2.step, program, clearControlsCfg, reverseOutputCfg, tapes,
    initialState, setControl, clearControl, controlIsNone]

theorem step_reverseOutput_cons
    (token : PairToken) (outputReverse output : List PairToken) :
    TM2.step program
        (reverseOutputCfg (token :: outputReverse) output) =
      some (reverseOutputCfg outputReverse (token :: output)) := by
  simp [TM2.step, program, reverseOutputCfg, tapes, initialState,
    setOutput, clearOutput, outputIsNone, outputFromState]
  funext stack
  cases stack <;> simp [tapes, Function.update]

theorem step_reverseOutput_nil (output : List PairToken) :
    TM2.step program (reverseOutputCfg [] output) =
      some (haltCfg output) := by
  simp [TM2.step, program, reverseOutputCfg, haltCfg, tapes,
    initialState, setOutput, clearOutput, outputIsNone]

end DelimitedBinaryWordPairBooleanFilterMachine
end LeanTrominoes

end
