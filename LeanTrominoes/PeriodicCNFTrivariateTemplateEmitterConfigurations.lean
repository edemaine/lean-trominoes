/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTrivariateTemplateEmitterMachine

/-! # Configurations for the trivariate template emitter -/

namespace LeanTrominoes

open StateTransition Turing

namespace PeriodicCNF
namespace TrivariateTemplateEmitterMachine

open UnaryProgramTokens

structure TapeData (Data : Type) where
  input : List (Workspace Data)
  first : List Unit
  second : List Unit
  remaining : List Unit
  processed : List Unit
  scratch : List Unit
  outputReverse : List (Workspace Data)
  output : List (Workspace Data)

def tapes {Data : Type} (data : TapeData Data) :
    ∀ stack, List (Alphabet Data stack)
  | .input => data.input
  | .first => data.first
  | .second => data.second
  | .remaining => data.remaining
  | .processed => data.processed
  | .scratch => data.scratch
  | .outputReverse => data.outputReverse
  | .output => data.output

def cfg {Data : Type} {recipes : List Recipe}
    (label : Label recipes.length) (state : State Data)
    (data : TapeData Data) :
    TM2.Cfg (Alphabet Data) (Label recipes.length) (State Data) :=
  ⟨some label, state, tapes data⟩

def scanCfg {Data : Type} {recipes : List Recipe} (data : TapeData Data) :=
  cfg (recipes := recipes) .scan none data

def beginPositionCfg {Data : Type} {recipes : List Recipe}
    (data : TapeData Data) :=
  cfg (recipes := recipes) .beginPosition none data

def executeCfg {Data : Type} {recipes : List Recipe}
    (index : Fin recipes.length) (data : TapeData Data) :=
  cfg (.execute index) none data

def scanFirstCfg {Data : Type} {recipes : List Recipe}
    (index : Fin recipes.length) (data : TapeData Data) :=
  cfg (.scanFirst index) none data

def restoreFirstCfg {Data : Type} {recipes : List Recipe}
    (index : Fin recipes.length) (data : TapeData Data) :=
  cfg (.restoreFirst index) none data

def scanSecondCfg {Data : Type} {recipes : List Recipe}
    (index : Fin recipes.length) (data : TapeData Data) :=
  cfg (.scanSecond index) none data

def restoreSecondCfg {Data : Type} {recipes : List Recipe}
    (index : Fin recipes.length) (data : TapeData Data) :=
  cfg (.restoreSecond index) none data

def scanPositionCfg {Data : Type} {recipes : List Recipe}
    (index : Fin recipes.length) (data : TapeData Data) :=
  cfg (.scanPosition index) none data

def restorePositionCfg {Data : Type} {recipes : List Recipe}
    (index : Fin recipes.length) (data : TapeData Data) :=
  cfg (.restorePosition index) none data

def emitEndingCfg {Data : Type} {recipes : List Recipe}
    (data : TapeData Data) :=
  cfg (recipes := recipes) .emitEnding none data

def clearFirstCfg {Data : Type} {recipes : List Recipe}
    (data : TapeData Data) :=
  cfg (recipes := recipes) .clearFirst none data

def clearSecondCfg {Data : Type} {recipes : List Recipe}
    (data : TapeData Data) :=
  cfg (recipes := recipes) .clearSecond none data

def clearProcessedCfg {Data : Type} {recipes : List Recipe}
    (data : TapeData Data) :=
  cfg (recipes := recipes) .clearProcessed none data

def reverseOutputCfg {Data : Type} {recipes : List Recipe}
    (data : TapeData Data) :=
  cfg (recipes := recipes) .reverseOutput none data

def haltCfg {Data : Type} {recipes : List Recipe}
    (output : List (Workspace Data)) :
    TM2.Cfg (Alphabet Data) (Label recipes.length) (State Data) :=
  ⟨none, none, tapes ⟨[], [], [], [], [], [], [], output⟩⟩

def haltDataCfg {Data : Type} {recipes : List Recipe}
    (data : TapeData Data) :
    TM2.Cfg (Alphabet Data) (Label recipes.length) (State Data) :=
  ⟨none, none, tapes data⟩

def afterRecipeCfg {Data : Type} (recipes : List Recipe)
    (index : Fin recipes.length) (data : TapeData Data) :
    TM2.Cfg (Alphabet Data) (Label recipes.length) (State Data) :=
  if nextExists : index.val + 1 < recipes.length then
    executeCfg ⟨index.val + 1, nextExists⟩ data
  else
    beginPositionCfg (recipes := recipes)
      { data with processed := () :: data.processed }

@[simp] theorem update_tapes_input {Data : Type} (data : TapeData Data)
    (value : List (Workspace Data)) :
    Function.update (tapes data) Stack.input value =
      tapes { data with input := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_first {Data : Type} (data : TapeData Data)
    (value : List Unit) :
    Function.update (tapes data) Stack.first value =
      tapes { data with first := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_second {Data : Type} (data : TapeData Data)
    (value : List Unit) :
    Function.update (tapes data) Stack.second value =
      tapes { data with second := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_remaining {Data : Type} (data : TapeData Data)
    (value : List Unit) :
    Function.update (tapes data) Stack.remaining value =
      tapes { data with remaining := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_processed {Data : Type} (data : TapeData Data)
    (value : List Unit) :
    Function.update (tapes data) Stack.processed value =
      tapes { data with processed := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_scratch {Data : Type} (data : TapeData Data)
    (value : List Unit) :
    Function.update (tapes data) Stack.scratch value =
      tapes { data with scratch := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_outputReverse {Data : Type}
    (data : TapeData Data) (value : List (Workspace Data)) :
    Function.update (tapes data) Stack.outputReverse value =
      tapes { data with outputReverse := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_output {Data : Type} (data : TapeData Data)
    (value : List (Workspace Data)) :
    Function.update (tapes data) Stack.output value =
      tapes { data with output := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

theorem stepAux_pushTokens {Data : Type} {recipes : List Recipe}
    (tokens : List Token)
    (next : TM2.Stmt (Alphabet Data) (Label recipes.length) (State Data))
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

theorem stepAux_pushAtomUnits {Data : Type} {recipes : List Recipe}
    (count : Nat)
    (next : TM2.Stmt (Alphabet Data) (Label recipes.length) (State Data))
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

end TrivariateTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
