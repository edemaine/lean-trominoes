/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIndexedTemplateEmitterPosition

/-!
# Complete indexed template recipe execution

Lift position scanning and restoration through one complete fixed or affine
recipe, with exact token output and runtime.
-/

namespace LeanTrominoes

open StateTransition Turing

namespace PeriodicCNF
namespace IndexedTemplateEmitterMachine

open AffineTemplateEmitterMachine
open IndexedTemplateEmitter
open UnaryProgramTokens

def oneStep {Configuration : Type}
    {transition : Configuration → Option Configuration}
    {first last : Configuration} (step : transition first = some last) :
    EvalsToInTime transition first (some last) 1 :=
  FiniteBlockTransducer.oneStep step

def scanPosition_evalsInTime {Data : Type} [Inhabited Data]
    (family : Family Data) (item : Data)
    (index : Fin (recipesFor family item).length) (base stride : Nat)
    (recipeEq : (recipesFor family item).get index = .atom base stride)
    (word : List Unit) (data : TapeData Data)
    (processedEq : data.processed = word) :
    EvalsToInTime (TM2.step (program family))
      (scanPositionCfg item index data)
      (some (restorePositionCfg item index
        { data with
          processed := []
          scratch := word.reverse ++ data.scratch
          tokenReverse :=
            List.replicate (stride * word.length) Token.atomUnit ++
              data.tokenReverse }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_scanPosition_nil family item index data processedEq)
      convert step using 1 <;> simp
  | cons element word induction =>
      have elementEq : element = () := Subsingleton.elim _ _
      subst element
      let nextData : TapeData Data :=
        { data with
          processed := word
          scratch := () :: data.scratch
          tokenReverse :=
            List.replicate stride Token.atomUnit ++ data.tokenReverse }
      have first := oneStep
        (step_scanPosition_cons_atom family item index base stride data word
          processedEq recipeEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans
        (TM2.step (program family))
        1 (word.length + 1) (scanPositionCfg item index data)
        (scanPositionCfg item index nextData)
        (some (restorePositionCfg item index
          { nextData with
            processed := []
            scratch := word.reverse ++ nextData.scratch
            tokenReverse :=
              List.replicate (stride * word.length) Token.atomUnit ++
                nextData.tokenReverse }))
        first rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
        rw [show stride * (word.length + 1) =
            stride * word.length + stride by ring,
          List.replicate_add, List.append_assoc]
      · simp

def restorePosition_evalsInTime {Data : Type} [Inhabited Data]
    (family : Family Data) (item : Data)
    (index : Fin (recipesFor family item).length)
    (word : List Unit) (data : TapeData Data)
    (scratchEq : data.scratch = word) :
    EvalsToInTime (TM2.step (program family))
      (restorePositionCfg item index data)
      (some (afterRecipeCfg family item index
        { data with
          processed := word.reverse ++ data.processed
          scratch := [] }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_restorePosition_nil family item index data scratchEq)
      convert step using 1 <;> simp
  | cons element word induction =>
      have elementEq : element = () := Subsingleton.elim _ _
      subst element
      let nextData : TapeData Data :=
        { data with
          processed := () :: data.processed
          scratch := word }
      have first := oneStep
        (step_restorePosition_cons family item index data word scratchEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans
        (TM2.step (program family))
        1 (word.length + 1) (restorePositionCfg item index data)
        (restorePositionCfg item index nextData)
        (some (afterRecipeCfg family item index
          { nextData with
            processed := word.reverse ++ nextData.processed
            scratch := [] }))
        first rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

def recipeTime (position : Nat) : Recipe → Nat
  | .fixed _ => 1
  | .atom _ _ => 2 * position + 3

def executeRecipe_evalsInTime {Data : Type} [Inhabited Data]
    (family : Family Data) (item : Data)
    (index : Fin (recipesFor family item).length) (position : Nat)
    (data : TapeData Data)
    (processedEq : data.processed = List.replicate position ())
    (scratchEq : data.scratch = []) :
    EvalsToInTime (TM2.step (program family))
      (executeCfg item index data)
      (some (afterRecipeCfg family item index
        { data with
          processed := List.replicate position ()
          scratch := []
          tokenReverse :=
            (Recipe.tokens position
              ((recipesFor family item).get index)).reverse ++
              data.tokenReverse }))
      (recipeTime position ((recipesFor family item).get index)) := by
  cases recipeEq : (recipesFor family item).get index with
  | fixed token =>
      have step := oneStep
        (step_execute_fixed family item index token data recipeEq)
      convert step using 1 <;>
        simp [Recipe.tokens, recipeTime, processedEq, scratchEq]
  | atom base stride =>
      let emittedData : TapeData Data :=
        { data with
          tokenReverse :=
            List.replicate base Token.atomUnit ++ data.tokenReverse }
      have first := oneStep
        (step_execute_atom family item index base stride data recipeEq)
      have scanned := scanPosition_evalsInTime family item index base stride
        recipeEq (List.replicate position ()) emittedData (by
          simpa [emittedData] using processedEq)
      let scannedData : TapeData Data :=
        { emittedData with
          processed := []
          scratch := (List.replicate position ()).reverse
          tokenReverse :=
            List.replicate (stride * position) Token.atomUnit ++
              emittedData.tokenReverse }
      have firstTwo := EvalsToInTime.trans
        (TM2.step (program family))
        1 (position + 1) (executeCfg item index data)
        (scanPositionCfg item index emittedData)
        (some (restorePositionCfg item index scannedData)) first (by
          simpa [scannedData, emittedData, scratchEq] using scanned)
      have restored := restorePosition_evalsInTime family item index
        (List.replicate position ()).reverse scannedData rfl
      have whole := EvalsToInTime.trans
        (TM2.step (program family))
        (position + 2) (position + 1) (executeCfg item index data)
        (restorePositionCfg item index scannedData)
        (some (afterRecipeCfg family item index
          { data with
            processed := List.replicate position ()
            scratch := []
            tokenReverse :=
              List.replicate (base + stride * position) Token.atomUnit ++
                data.tokenReverse }))
        firstTwo (by
          have outputEq :
              List.replicate (base + stride * position) Token.atomUnit ++
                  data.tokenReverse =
                List.replicate (stride * position) Token.atomUnit ++
                  (List.replicate base Token.atomUnit ++
                    data.tokenReverse) := by
            rw [← List.append_assoc, ← List.replicate_add]
            congr 2
            ring
          convert restored using 1
          · simp [scannedData, emittedData, outputEq]
          · simp)
      convert whole using 1
      · simp [Recipe.tokens]
      · simp [recipeTime]
        ring

end IndexedTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
