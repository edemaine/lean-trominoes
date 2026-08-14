/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIndexedTemplateEmitterMachine

/-!
# Invariant configurations for the indexed template emitter

Named configuration constructors and exact dependent-stack update identities
for the scan, recipe, position-rescan, cleanup, and reversal proofs.
-/

namespace LeanTrominoes

open StateTransition Turing

namespace PeriodicCNF
namespace IndexedTemplateEmitterMachine

open IndexedTemplateEmitter

structure TapeData (Data : Type) where
  input : List Data
  inputReverse : List Data
  processed : List Unit
  scratch : List Unit
  tokenReverse : List UnaryProgramTokens.Token
  output : List (Data ⊕ UnaryProgramTokens.Token)

def tapes {Data : Type} (data : TapeData Data) :
    ∀ stack, List (Alphabet Data stack)
  | .input => data.input
  | .inputReverse => data.inputReverse
  | .processed => data.processed
  | .scratch => data.scratch
  | .tokenReverse => data.tokenReverse
  | .output => data.output

def cfg {Data : Type} {family : Family Data}
    (label : Label Data family) (state : State Data) (data : TapeData Data) :
    TM2.Cfg (Alphabet Data) (Label Data family) (State Data) :=
  ⟨some label, state, tapes data⟩

def scanCfg {Data : Type} {family : Family Data} (data : TapeData Data) :=
  cfg (family := family) .scan none data

def beginItemCfg {Data : Type} {family : Family Data} (item : Data)
    (data : TapeData Data) :=
  cfg (family := family) (.beginItem item) (some (.inl item)) data

def executeCfg {Data : Type} {family : Family Data} (item : Data)
    (index : Fin (recipesFor family item).length) (data : TapeData Data) :=
  cfg (.execute item index) none data

def scanPositionCfg {Data : Type} {family : Family Data} (item : Data)
    (index : Fin (recipesFor family item).length) (data : TapeData Data) :=
  cfg (.scanPosition item index) none data

def restorePositionCfg {Data : Type} {family : Family Data} (item : Data)
    (index : Fin (recipesFor family item).length) (data : TapeData Data) :=
  cfg (.restorePosition item index) none data

def clearProcessedCfg {Data : Type} {family : Family Data}
    (data : TapeData Data) :=
  cfg (family := family) .clearProcessed none data

def reverseTokensCfg {Data : Type} {family : Family Data}
    (data : TapeData Data) :=
  cfg (family := family) .reverseTokens none data

def reverseInputCfg {Data : Type} {family : Family Data}
    (data : TapeData Data) :=
  cfg (family := family) .reverseInput none data

def haltCfg {Data : Type} {family : Family Data}
    (output : List (Data ⊕ UnaryProgramTokens.Token)) :
    TM2.Cfg (Alphabet Data) (Label Data family) (State Data) :=
  ⟨none, none, tapes ⟨[], [], [], [], [], output⟩⟩

def haltDataCfg {Data : Type} {family : Family Data}
    (data : TapeData Data) :
    TM2.Cfg (Alphabet Data) (Label Data family) (State Data) :=
  ⟨none, none, tapes data⟩

def afterRecipeCfg {Data : Type} (family : Family Data) (item : Data)
    (index : Fin (recipesFor family item).length) (data : TapeData Data) :
    TM2.Cfg (Alphabet Data) (Label Data family) (State Data) :=
  if nextExists : index.val + 1 < (recipesFor family item).length then
    executeCfg item ⟨index.val + 1, nextExists⟩ data
  else
    scanCfg (family := family)
      { data with processed := () :: data.processed }

@[simp]
theorem update_tapes_input {Data : Type} (data : TapeData Data)
    (value : List Data) :
    Function.update (tapes data) Stack.input value =
      tapes { data with input := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp]
theorem update_tapes_inputReverse {Data : Type} (data : TapeData Data)
    (value : List Data) :
    Function.update (tapes data) Stack.inputReverse value =
      tapes { data with inputReverse := value } := by
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
theorem update_tapes_scratch {Data : Type} (data : TapeData Data)
    (value : List Unit) :
    Function.update (tapes data) Stack.scratch value =
      tapes { data with scratch := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp]
theorem update_tapes_tokenReverse {Data : Type} (data : TapeData Data)
    (value : List UnaryProgramTokens.Token) :
    Function.update (tapes data) Stack.tokenReverse value =
      tapes { data with tokenReverse := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp]
theorem update_tapes_output {Data : Type} (data : TapeData Data)
    (value : List (Data ⊕ UnaryProgramTokens.Token)) :
    Function.update (tapes data) Stack.output value =
      tapes { data with output := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp]
theorem dataFromState_some {Data : Type} [Inhabited Data] (data : Data) :
    dataFromState (some (.inl data)) = data :=
  rfl

@[simp]
theorem tokenFromState_some {Data : Type}
    (token : UnaryProgramTokens.Token) :
    tokenFromState (Data := Data) (some (.inr (.inr token))) = token :=
  rfl

end IndexedTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
