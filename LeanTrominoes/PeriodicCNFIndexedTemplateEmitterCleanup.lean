/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIndexedTemplateEmitterInput

/-!
# Indexed template emitter cleanup and output reversal

Clear the unary selected-position counter, reverse emitted tokens into forward
order, then reverse retained input in front of those tokens and halt.
-/

namespace LeanTrominoes

open StateTransition Turing

namespace PeriodicCNF
namespace IndexedTemplateEmitterMachine

open IndexedTemplateEmitter
open UnaryProgramTokens

theorem step_clearProcessed_nil {Data : Type} [Inhabited Data]
    (family : Family Data) (data : TapeData Data)
    (processedEq : data.processed = []) :
    TM2.step (program family) (clearProcessedCfg data) =
      some (reverseTokensCfg { data with processed := [] }) := by
  rcases data with
    ⟨input, inputReverse, processed, scratch, tokenReverse, output⟩
  change processed = [] at processedEq
  subst processed
  simp [TM2.step, program, clearProcessedCfg, reverseTokensCfg, cfg, tapes]

theorem step_clearProcessed_cons {Data : Type} [Inhabited Data]
    (family : Family Data) (data : TapeData Data) (tail : List Unit)
    (processedEq : data.processed = () :: tail) :
    TM2.step (program family) (clearProcessedCfg data) =
      some (clearProcessedCfg { data with processed := tail }) := by
  rcases data with
    ⟨input, inputReverse, processed, scratch, tokenReverse, output⟩
  change processed = () :: tail at processedEq
  subst processed
  simp [TM2.step, program, clearProcessedCfg, cfg, tapes]

theorem step_reverseTokens_nil {Data : Type} [Inhabited Data]
    (family : Family Data) (data : TapeData Data)
    (tokensEq : data.tokenReverse = []) :
    TM2.step (program family) (reverseTokensCfg data) =
      some (reverseInputCfg { data with tokenReverse := [] }) := by
  rcases data with
    ⟨input, inputReverse, processed, scratch, tokenReverse, output⟩
  change tokenReverse = [] at tokensEq
  subst tokenReverse
  simp [TM2.step, program, reverseTokensCfg, reverseInputCfg, cfg, tapes]

theorem step_reverseTokens_cons {Data : Type} [Inhabited Data]
    (family : Family Data) (data : TapeData Data) (token : Token)
    (tail : List Token) (tokensEq : data.tokenReverse = token :: tail) :
    TM2.step (program family) (reverseTokensCfg data) =
      some (reverseTokensCfg
        { data with
          tokenReverse := tail
          output := (Sum.inr token : Data ⊕ Token) :: data.output }) := by
  rcases data with
    ⟨input, inputReverse, processed, scratch, tokenReverse, output⟩
  change tokenReverse = token :: tail at tokensEq
  subst tokenReverse
  simp [TM2.step, program, reverseTokensCfg, cfg, tapes,
    tokenFromState]

theorem step_reverseInput_nil {Data : Type} [Inhabited Data]
    (family : Family Data) (data : TapeData Data)
    (inputEq : data.inputReverse = []) :
    TM2.step (program family) (reverseInputCfg data) =
      some (haltDataCfg { data with inputReverse := [] }) := by
  rcases data with
    ⟨input, inputReverse, processed, scratch, tokenReverse, output⟩
  change inputReverse = [] at inputEq
  subst inputReverse
  simp [TM2.step, program, reverseInputCfg, haltDataCfg, cfg, tapes]

theorem step_reverseInput_cons {Data : Type} [Inhabited Data]
    (family : Family Data) (data : TapeData Data) (item : Data)
    (tail : List Data) (inputEq : data.inputReverse = item :: tail) :
    TM2.step (program family) (reverseInputCfg data) =
      some (reverseInputCfg
        { data with
          inputReverse := tail
          output := (Sum.inl item : Data ⊕ Token) :: data.output }) := by
  rcases data with
    ⟨input, inputReverse, processed, scratch, tokenReverse, output⟩
  change inputReverse = item :: tail at inputEq
  subst inputReverse
  simp [TM2.step, program, reverseInputCfg, cfg, tapes, dataFromState]

def clearProcessed_evalsInTime {Data : Type} [Inhabited Data]
    (family : Family Data) (word : List Unit) (data : TapeData Data)
    (processedEq : data.processed = word) :
    EvalsToInTime (TM2.step (program family))
      (clearProcessedCfg data)
      (some (reverseTokensCfg { data with processed := [] }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_clearProcessed_nil family data processedEq)
      simpa using step
  | cons element word induction =>
      have elementEq : element = () := Subsingleton.elim _ _
      subst element
      let nextData : TapeData Data := { data with processed := word }
      have first := oneStep
        (step_clearProcessed_cons family data word processedEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans
        (TM2.step (program family))
        1 (word.length + 1) (clearProcessedCfg data)
        (clearProcessedCfg nextData)
        (some (reverseTokensCfg { nextData with processed := [] }))
        first rest
      simpa using composed

def reverseTokens_evalsInTime {Data : Type} [Inhabited Data]
    (family : Family Data) (word : List Token) (data : TapeData Data)
    (tokensEq : data.tokenReverse = word) :
    EvalsToInTime (TM2.step (program family))
      (reverseTokensCfg data)
      (some (reverseInputCfg
        { data with
          tokenReverse := []
          output := word.reverse.map Sum.inr ++ data.output }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep (step_reverseTokens_nil family data tokensEq)
      convert step using 1 <;> simp
  | cons token word induction =>
      let nextData : TapeData Data :=
        { data with
          tokenReverse := word
          output := (Sum.inr token : Data ⊕ Token) :: data.output }
      have first := oneStep
        (step_reverseTokens_cons family data token word tokensEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans
        (TM2.step (program family))
        1 (word.length + 1) (reverseTokensCfg data)
        (reverseTokensCfg nextData)
        (some (reverseInputCfg
          { nextData with
            tokenReverse := []
            output := word.reverse.map Sum.inr ++ nextData.output }))
        first rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.map_append,
          List.append_assoc]
      · simp

def reverseInput_evalsInTime {Data : Type} [Inhabited Data]
    (family : Family Data) (word : List Data) (data : TapeData Data)
    (inputEq : data.inputReverse = word) :
    EvalsToInTime (TM2.step (program family))
      (reverseInputCfg data)
      (some (haltDataCfg
        { data with
          inputReverse := []
          output := word.reverse.map Sum.inl ++ data.output }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep (step_reverseInput_nil family data inputEq)
      convert step using 1 <;> simp
  | cons item word induction =>
      let nextData : TapeData Data :=
        { data with
          inputReverse := word
          output := (Sum.inl item : Data ⊕ Token) :: data.output }
      have first := oneStep
        (step_reverseInput_cons family data item word inputEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans
        (TM2.step (program family))
        1 (word.length + 1) (reverseInputCfg data)
        (reverseInputCfg nextData)
        (some (haltDataCfg
          { nextData with
            inputReverse := []
            output := word.reverse.map Sum.inl ++ nextData.output }))
        first rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.map_append,
          List.append_assoc]
      · simp

end IndexedTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
