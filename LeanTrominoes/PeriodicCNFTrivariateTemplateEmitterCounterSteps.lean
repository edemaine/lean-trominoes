/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTrivariateTemplateEmitterConfigurations

/-! # Counter-loop steps for the trivariate template emitter -/

namespace LeanTrominoes

open Turing

namespace PeriodicCNF
namespace TrivariateTemplateEmitterMachine

open UnaryProgramTokens

theorem step_scanFirst_nil {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length) (data : TapeData Data)
    (firstEq : data.first = []) :
    TM2.step
        (program firstSelected secondSelected positionSelected recipes ending)
        (scanFirstCfg index data) =
      some (restoreFirstCfg index { data with first := [] }) := by
  rcases data with
    ⟨input, first, second, remaining, processed, scratch,
      outputReverse, output⟩
  change first = [] at firstEq
  subst first
  simp [TM2.step, program, scanFirstCfg, restoreFirstCfg, cfg, tapes]

theorem step_scanFirst_cons_atom {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length)
    (base firstStride secondStride positionStride : Nat)
    (data : TapeData Data) (tail : List Unit)
    (firstEq : data.first = () :: tail)
    (recipeEq : recipes.get index =
      .atom base firstStride secondStride positionStride) :
    TM2.step
        (program firstSelected secondSelected positionSelected recipes ending)
        (scanFirstCfg index data) =
      some (scanFirstCfg index
        { data with
          first := tail
          scratch := () :: data.scratch
          outputReverse :=
            List.replicate firstStride
                (Sum.inr Token.atomUnit : Workspace Data) ++
              data.outputReverse }) := by
  rcases data with
    ⟨input, first, second, remaining, processed, scratch,
      outputReverse, output⟩
  change first = () :: tail at firstEq
  subst first
  simp only [TM2.step, program, scanFirstCfg, cfg]
  rw [recipeEq]
  simp only [TM2.stepAux, update_tapes_first, update_tapes_scratch]
  rw [stepAux_pushAtomUnits]
  rfl

theorem step_restoreFirst_nil {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length) (data : TapeData Data)
    (scratchEq : data.scratch = []) :
    TM2.step
        (program firstSelected secondSelected positionSelected recipes ending)
        (restoreFirstCfg index data) =
      some (scanSecondCfg index { data with scratch := [] }) := by
  rcases data with
    ⟨input, first, second, remaining, processed, scratch,
      outputReverse, output⟩
  change scratch = [] at scratchEq
  subst scratch
  simp [TM2.step, program, restoreFirstCfg, scanSecondCfg, cfg, tapes]

theorem step_restoreFirst_cons {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length) (data : TapeData Data) (tail : List Unit)
    (scratchEq : data.scratch = () :: tail) :
    TM2.step
        (program firstSelected secondSelected positionSelected recipes ending)
        (restoreFirstCfg index data) =
      some (restoreFirstCfg index
        { data with
          first := () :: data.first
          scratch := tail }) := by
  rcases data with
    ⟨input, first, second, remaining, processed, scratch,
      outputReverse, output⟩
  change scratch = () :: tail at scratchEq
  subst scratch
  simp [TM2.step, program, restoreFirstCfg, cfg, tapes]

theorem step_scanSecond_nil {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length) (data : TapeData Data)
    (secondEq : data.second = []) :
    TM2.step
        (program firstSelected secondSelected positionSelected recipes ending)
        (scanSecondCfg index data) =
      some (restoreSecondCfg index { data with second := [] }) := by
  rcases data with
    ⟨input, first, second, remaining, processed, scratch,
      outputReverse, output⟩
  change second = [] at secondEq
  subst second
  simp [TM2.step, program, scanSecondCfg, restoreSecondCfg, cfg, tapes]

theorem step_scanSecond_cons_atom {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length)
    (base firstStride secondStride positionStride : Nat)
    (data : TapeData Data) (tail : List Unit)
    (secondEq : data.second = () :: tail)
    (recipeEq : recipes.get index =
      .atom base firstStride secondStride positionStride) :
    TM2.step
        (program firstSelected secondSelected positionSelected recipes ending)
        (scanSecondCfg index data) =
      some (scanSecondCfg index
        { data with
          second := tail
          scratch := () :: data.scratch
          outputReverse :=
            List.replicate secondStride
                (Sum.inr Token.atomUnit : Workspace Data) ++
              data.outputReverse }) := by
  rcases data with
    ⟨input, first, second, remaining, processed, scratch,
      outputReverse, output⟩
  change second = () :: tail at secondEq
  subst second
  simp only [TM2.step, program, scanSecondCfg, cfg]
  rw [recipeEq]
  simp only [TM2.stepAux, update_tapes_second, update_tapes_scratch]
  rw [stepAux_pushAtomUnits]
  rfl

theorem step_restoreSecond_nil {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length) (data : TapeData Data)
    (scratchEq : data.scratch = []) :
    TM2.step
        (program firstSelected secondSelected positionSelected recipes ending)
        (restoreSecondCfg index data) =
      some (scanPositionCfg index { data with scratch := [] }) := by
  rcases data with
    ⟨input, first, second, remaining, processed, scratch,
      outputReverse, output⟩
  change scratch = [] at scratchEq
  subst scratch
  simp [TM2.step, program, restoreSecondCfg, scanPositionCfg, cfg, tapes]

theorem step_restoreSecond_cons {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length) (data : TapeData Data) (tail : List Unit)
    (scratchEq : data.scratch = () :: tail) :
    TM2.step
        (program firstSelected secondSelected positionSelected recipes ending)
        (restoreSecondCfg index data) =
      some (restoreSecondCfg index
        { data with
          second := () :: data.second
          scratch := tail }) := by
  rcases data with
    ⟨input, first, second, remaining, processed, scratch,
      outputReverse, output⟩
  change scratch = () :: tail at scratchEq
  subst scratch
  simp [TM2.step, program, restoreSecondCfg, cfg, tapes]

theorem step_scanPosition_nil {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length) (data : TapeData Data)
    (processedEq : data.processed = []) :
    TM2.step
        (program firstSelected secondSelected positionSelected recipes ending)
        (scanPositionCfg index data) =
      some (restorePositionCfg index { data with processed := [] }) := by
  rcases data with
    ⟨input, first, second, remaining, processed, scratch,
      outputReverse, output⟩
  change processed = [] at processedEq
  subst processed
  simp [TM2.step, program, scanPositionCfg, restorePositionCfg, cfg, tapes]

theorem step_scanPosition_cons_atom {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length)
    (base firstStride secondStride positionStride : Nat)
    (data : TapeData Data) (tail : List Unit)
    (processedEq : data.processed = () :: tail)
    (recipeEq : recipes.get index =
      .atom base firstStride secondStride positionStride) :
    TM2.step
        (program firstSelected secondSelected positionSelected recipes ending)
        (scanPositionCfg index data) =
      some (scanPositionCfg index
        { data with
          processed := tail
          scratch := () :: data.scratch
          outputReverse :=
            List.replicate positionStride
                (Sum.inr Token.atomUnit : Workspace Data) ++
              data.outputReverse }) := by
  rcases data with
    ⟨input, first, second, remaining, processed, scratch,
      outputReverse, output⟩
  change processed = () :: tail at processedEq
  subst processed
  simp only [TM2.step, program, scanPositionCfg, cfg]
  rw [recipeEq]
  simp only [TM2.stepAux, update_tapes_processed, update_tapes_scratch]
  rw [stepAux_pushAtomUnits]
  rfl

theorem step_restorePosition_nil {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length) (data : TapeData Data)
    (scratchEq : data.scratch = []) :
    TM2.step
        (program firstSelected secondSelected positionSelected recipes ending)
        (restorePositionCfg index data) =
      some (afterRecipeCfg recipes index { data with scratch := [] }) := by
  rcases data with
    ⟨input, first, second, remaining, processed, scratch,
      outputReverse, output⟩
  change scratch = [] at scratchEq
  subst scratch
  by_cases nextExists : index.val + 1 < recipes.length
  · simp [TM2.step, program, restorePositionCfg, afterRecipe,
      afterRecipeCfg, nextExists, executeCfg, cfg, tapes]
  · simp [TM2.step, program, restorePositionCfg, afterRecipe,
      afterRecipeCfg, nextExists, beginPositionCfg, cfg, tapes]

theorem step_restorePosition_cons {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length) (data : TapeData Data) (tail : List Unit)
    (scratchEq : data.scratch = () :: tail) :
    TM2.step
        (program firstSelected secondSelected positionSelected recipes ending)
        (restorePositionCfg index data) =
      some (restorePositionCfg index
        { data with
          processed := () :: data.processed
          scratch := tail }) := by
  rcases data with
    ⟨input, first, second, remaining, processed, scratch,
      outputReverse, output⟩
  change scratch = () :: tail at scratchEq
  subst scratch
  simp [TM2.step, program, restorePositionCfg, cfg, tapes]

end TrivariateTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
