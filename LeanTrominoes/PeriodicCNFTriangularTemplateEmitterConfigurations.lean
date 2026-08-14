/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTriangularTemplateEmitterMachine

/-!
# Configurations of the triangular template emitter

Named invariant configurations and stack-update identities are kept separate
from execution induction.  This file also proves the two generic output-push
lemmas used by every later recipe, frame, and cleanup phase.
-/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF
namespace TriangularTemplateEmitterMachine

open UnaryProgramTokens

structure TapeData (Data : Type) where
  input : List (Workspace Data)
  first : List Unit
  remaining : List Unit
  current : List Unit
  processed : List Unit
  innerProcessed : List Unit
  firstScratch : List Unit
  positionScratch : List Unit
  outputReverse : List (Workspace Data)
  output : List (Workspace Data)

def tapes {Data : Type} (data : TapeData Data) :
    ∀ stack, List (Alphabet Data stack)
  | .input => data.input
  | .first => data.first
  | .remaining => data.remaining
  | .current => data.current
  | .processed => data.processed
  | .innerProcessed => data.innerProcessed
  | .firstScratch => data.firstScratch
  | .positionScratch => data.positionScratch
  | .outputReverse => data.outputReverse
  | .output => data.output

def cfg {Data : Type}
    {outerFirst inner outerSecond : List Recipe}
    (label : Label outerFirst.length inner.length outerSecond.length)
    (state : State Data) (data : TapeData Data) :
    TM2.Cfg (Alphabet Data)
      (Label outerFirst.length inner.length outerSecond.length) (State Data) :=
  ⟨some label, state, tapes data⟩

def scanCfg {Data : Type}
    {outerFirst inner outerSecond : List Recipe} (data : TapeData Data) :=
  cfg (outerFirst := outerFirst) (inner := inner)
    (outerSecond := outerSecond) .scan none data

def beginOuterCfg {Data : Type}
    {outerFirst inner outerSecond : List Recipe} (data : TapeData Data) :=
  cfg (outerFirst := outerFirst) (inner := inner)
    (outerSecond := outerSecond) .beginOuter none data

def beginInnerCfg {Data : Type}
    {outerFirst inner outerSecond : List Recipe} (data : TapeData Data) :=
  cfg (outerFirst := outerFirst) (inner := inner)
    (outerSecond := outerSecond) .beginInner none data

def executeCfg {Data : Type}
    (outerFirst inner outerSecond : List Recipe) (stage : Stage)
    (index : Fin (stageCount outerFirst inner outerSecond stage))
    (data : TapeData Data) :=
  cfg (stageLabel outerFirst inner outerSecond stage index) none data

def scanFirstCfg {Data : Type}
    (outerFirst inner outerSecond : List Recipe) (stage : Stage)
    (index : Fin (stageCount outerFirst inner outerSecond stage))
    (data : TapeData Data) :=
  cfg (scanFirstLabel outerFirst inner outerSecond stage index) none data

def restoreFirstCfg {Data : Type}
    (outerFirst inner outerSecond : List Recipe) (stage : Stage)
    (index : Fin (stageCount outerFirst inner outerSecond stage))
    (data : TapeData Data) :=
  cfg (restoreFirstLabel outerFirst inner outerSecond stage index) none data

def scanPositionCfg {Data : Type}
    (outerFirst inner outerSecond : List Recipe) (stage : Stage)
    (index : Fin (stageCount outerFirst inner outerSecond stage))
    (data : TapeData Data) :=
  cfg (scanPositionLabel outerFirst inner outerSecond stage index) none data

def restorePositionCfg {Data : Type}
    (outerFirst inner outerSecond : List Recipe) (stage : Stage)
    (index : Fin (stageCount outerFirst inner outerSecond stage))
    (data : TapeData Data) :=
  cfg (restorePositionLabel outerFirst inner outerSecond stage index) none data

def scanInnerCfg {Data : Type}
    {outerFirst inner outerSecond : List Recipe}
    (index : Fin inner.length) (data : TapeData Data) :=
  cfg (outerFirst := outerFirst) (inner := inner)
    (outerSecond := outerSecond) (.scanInner index) none data

def restoreInnerCfg {Data : Type}
    {outerFirst inner outerSecond : List Recipe}
    (index : Fin inner.length) (data : TapeData Data) :=
  cfg (outerFirst := outerFirst) (inner := inner)
    (outerSecond := outerSecond) (.restoreInner index) none data

def finishInnerPositionCfg {Data : Type}
    {outerFirst inner outerSecond : List Recipe} (data : TapeData Data) :=
  cfg (outerFirst := outerFirst) (inner := inner)
    (outerSecond := outerSecond) .finishInnerPosition none data

def restoreInnerRangeCfg {Data : Type}
    {outerFirst inner outerSecond : List Recipe} (data : TapeData Data) :=
  cfg (outerFirst := outerFirst) (inner := inner)
    (outerSecond := outerSecond) .restoreInnerRange none data

def finishOuterCfg {Data : Type}
    {outerFirst inner outerSecond : List Recipe} (data : TapeData Data) :=
  cfg (outerFirst := outerFirst) (inner := inner)
    (outerSecond := outerSecond) .finishOuter none data

def unwindCfg {Data : Type}
    {outerFirst inner outerSecond : List Recipe} (data : TapeData Data) :=
  cfg (outerFirst := outerFirst) (inner := inner)
    (outerSecond := outerSecond) .unwind none data

def clearFirstCfg {Data : Type}
    {outerFirst inner outerSecond : List Recipe} (data : TapeData Data) :=
  cfg (outerFirst := outerFirst) (inner := inner)
    (outerSecond := outerSecond) .clearFirst none data

def reverseOutputCfg {Data : Type}
    {outerFirst inner outerSecond : List Recipe} (data : TapeData Data) :=
  cfg (outerFirst := outerFirst) (inner := inner)
    (outerSecond := outerSecond) .reverseOutput none data

def haltCfg {Data : Type}
    {outerFirst inner outerSecond : List Recipe}
    (output : List (Workspace Data)) :
    TM2.Cfg (Alphabet Data)
      (Label outerFirst.length inner.length outerSecond.length) (State Data) :=
  ⟨none, none, tapes ⟨[], [], [], [], [], [], [], [], [], output⟩⟩

def haltDataCfg {Data : Type}
    {outerFirst inner outerSecond : List Recipe} (data : TapeData Data) :
    TM2.Cfg (Alphabet Data)
      (Label outerFirst.length inner.length outerSecond.length) (State Data) :=
  ⟨none, none, tapes data⟩

@[simp]
theorem update_tapes_input {Data : Type} (data : TapeData Data)
    (value : List (Workspace Data)) :
    Function.update (tapes data) Stack.input value =
      tapes { data with input := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp]
theorem update_tapes_first {Data : Type} (data : TapeData Data)
    (value : List Unit) :
    Function.update (tapes data) Stack.first value =
      tapes { data with first := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp]
theorem update_tapes_remaining {Data : Type} (data : TapeData Data)
    (value : List Unit) :
    Function.update (tapes data) Stack.remaining value =
      tapes { data with remaining := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp]
theorem update_tapes_current {Data : Type} (data : TapeData Data)
    (value : List Unit) :
    Function.update (tapes data) Stack.current value =
      tapes { data with current := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp]
theorem update_tapes_processed {Data : Type} (data : TapeData Data)
    (value : List Unit) :
    Function.update (tapes data) Stack.processed value =
      tapes { data with processed := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp]
theorem update_tapes_innerProcessed {Data : Type} (data : TapeData Data)
    (value : List Unit) :
    Function.update (tapes data) Stack.innerProcessed value =
      tapes { data with innerProcessed := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp]
theorem update_tapes_firstScratch {Data : Type} (data : TapeData Data)
    (value : List Unit) :
    Function.update (tapes data) Stack.firstScratch value =
      tapes { data with firstScratch := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp]
theorem update_tapes_positionScratch {Data : Type} (data : TapeData Data)
    (value : List Unit) :
    Function.update (tapes data) Stack.positionScratch value =
      tapes { data with positionScratch := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp]
theorem update_tapes_outputReverse {Data : Type} (data : TapeData Data)
    (value : List (Workspace Data)) :
    Function.update (tapes data) Stack.outputReverse value =
      tapes { data with outputReverse := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp]
theorem update_tapes_output {Data : Type} (data : TapeData Data)
    (value : List (Workspace Data)) :
    Function.update (tapes data) Stack.output value =
      tapes { data with output := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

theorem stepAux_pushTokens {Data : Type}
    {outerFirstCount innerCount outerSecondCount : Nat}
    (tokens : List Token)
    (next : TM2.Stmt (Alphabet Data)
      (Label outerFirstCount innerCount outerSecondCount) (State Data))
    (state : State Data) (data : TapeData Data) :
    TM2.stepAux (pushTokens tokens next) state (tapes data) =
      TM2.stepAux next state
        (tapes { data with
          outputReverse :=
            (tokens.map fun token =>
              (Sum.inr token : Workspace Data)).reverse ++
                data.outputReverse }) := by
  induction tokens generalizing data with
  | nil => simp [pushTokens]
  | cons token tokens induction =>
      simp only [pushTokens, List.foldr_cons, TM2.stepAux]
      rw [update_tapes_outputReverse]
      change TM2.stepAux (pushTokens tokens next) state
          (tapes { data with
            outputReverse :=
              (Sum.inr token : Workspace Data) :: data.outputReverse }) = _
      rw [induction]
      simp [List.reverse_cons, List.append_assoc]

theorem stepAux_pushAtomUnits {Data : Type}
    {outerFirstCount innerCount outerSecondCount : Nat}
    (count : Nat)
    (next : TM2.Stmt (Alphabet Data)
      (Label outerFirstCount innerCount outerSecondCount) (State Data))
    (state : State Data) (data : TapeData Data) :
    TM2.stepAux (pushAtomUnits count next) state (tapes data) =
      TM2.stepAux next state
        (tapes { data with
          outputReverse :=
            List.replicate count
                (Sum.inr Token.atomUnit : Workspace Data) ++
              data.outputReverse }) := by
  rw [pushAtomUnits, stepAux_pushTokens]
  simp

end TriangularTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
