/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTrivariateTemplateEmitterConfigurations

/-! # Boundary and cleanup steps for the trivariate template emitter -/

namespace LeanTrominoes

open Turing

namespace PeriodicCNF
namespace TrivariateTemplateEmitterMachine

open UnaryProgramTokens

theorem step_beginPosition_nil {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (data : TapeData Data) (remainingEq : data.remaining = []) :
    TM2.step
        (program firstSelected secondSelected positionSelected recipes ending)
        (beginPositionCfg data) =
      some (emitEndingCfg { data with remaining := [] }) := by
  rcases data with
    ⟨input, first, second, remaining, processed, scratch,
      outputReverse, output⟩
  change remaining = [] at remainingEq
  subst remaining
  simp [TM2.step, program, beginPositionCfg, emitEndingCfg, cfg, tapes]

theorem step_beginPosition_cons_nonempty {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (nonempty : 0 < recipes.length) (data : TapeData Data)
    (tail : List Unit) (remainingEq : data.remaining = () :: tail) :
    TM2.step
        (program firstSelected secondSelected positionSelected recipes ending)
        (beginPositionCfg data) =
      some (executeCfg ⟨0, nonempty⟩ { data with remaining := tail }) := by
  rcases data with
    ⟨input, first, second, remaining, processed, scratch,
      outputReverse, output⟩
  change remaining = () :: tail at remainingEq
  subst remaining
  simp [TM2.step, program, beginTemplate, nonempty,
    beginPositionCfg, executeCfg, cfg, tapes]

theorem step_beginPosition_cons_empty {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (empty : recipes = []) (data : TapeData Data)
    (tail : List Unit) (remainingEq : data.remaining = () :: tail) :
    TM2.step
        (program firstSelected secondSelected positionSelected recipes ending)
        (beginPositionCfg data) =
      some (beginPositionCfg
        { data with
          remaining := tail
          processed := () :: data.processed }) := by
  subst recipes
  rcases data with
    ⟨input, first, second, remaining, processed, scratch,
      outputReverse, output⟩
  change remaining = () :: tail at remainingEq
  subst remaining
  simp [TM2.step, program, beginTemplate, beginPositionCfg, cfg, tapes]

theorem step_execute_fixed {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length) (token : Token) (data : TapeData Data)
    (recipeEq : recipes.get index = .fixed token) :
    TM2.step
        (program firstSelected secondSelected positionSelected recipes ending)
        (executeCfg index data) =
      some (afterRecipeCfg recipes index
        { data with
          outputReverse :=
            (Sum.inr token : Workspace Data) :: data.outputReverse }) := by
  simp only [TM2.step, program, executeCfg, cfg]
  rw [recipeEq]
  by_cases nextExists : index.val + 1 < recipes.length
  · simp [afterRecipe, afterRecipeCfg, nextExists, executeCfg, cfg, tapes]
  · simp [afterRecipe, afterRecipeCfg, nextExists,
      beginPositionCfg, cfg, tapes]

theorem step_execute_atom {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length)
    (base firstStride secondStride positionStride : Nat)
    (data : TapeData Data)
    (recipeEq : recipes.get index =
      .atom base firstStride secondStride positionStride) :
    TM2.step
        (program firstSelected secondSelected positionSelected recipes ending)
        (executeCfg index data) =
      some (scanFirstCfg index
        { data with
          outputReverse :=
            List.replicate base
                (Sum.inr Token.atomUnit : Workspace Data) ++
              data.outputReverse }) := by
  simp only [TM2.step, program, executeCfg, scanFirstCfg, cfg]
  rw [recipeEq, stepAux_pushAtomUnits]
  rfl

theorem step_emitEnding {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token) (data : TapeData Data) :
    TM2.step
        (program firstSelected secondSelected positionSelected recipes ending)
        (emitEndingCfg data) =
      some (clearFirstCfg
        { data with
          outputReverse :=
            (ending.map fun token =>
              (Sum.inr token : Workspace Data)).reverse ++
                data.outputReverse }) := by
  simp only [TM2.step, program, emitEndingCfg, clearFirstCfg, cfg]
  rw [stepAux_pushTokens]
  rfl

theorem step_clearFirst_nil {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (data : TapeData Data) (firstEq : data.first = []) :
    TM2.step
        (program firstSelected secondSelected positionSelected recipes ending)
        (clearFirstCfg data) =
      some (clearSecondCfg { data with first := [] }) := by
  rcases data with
    ⟨input, first, second, remaining, processed, scratch,
      outputReverse, output⟩
  change first = [] at firstEq
  subst first
  simp [TM2.step, program, clearFirstCfg, clearSecondCfg, cfg, tapes]

theorem step_clearFirst_cons {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (data : TapeData Data) (tail : List Unit)
    (firstEq : data.first = () :: tail) :
    TM2.step
        (program firstSelected secondSelected positionSelected recipes ending)
        (clearFirstCfg data) =
      some (clearFirstCfg { data with first := tail }) := by
  rcases data with
    ⟨input, first, second, remaining, processed, scratch,
      outputReverse, output⟩
  change first = () :: tail at firstEq
  subst first
  simp [TM2.step, program, clearFirstCfg, cfg, tapes]

theorem step_clearSecond_nil {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (data : TapeData Data) (secondEq : data.second = []) :
    TM2.step
        (program firstSelected secondSelected positionSelected recipes ending)
        (clearSecondCfg data) =
      some (clearProcessedCfg { data with second := [] }) := by
  rcases data with
    ⟨input, first, second, remaining, processed, scratch,
      outputReverse, output⟩
  change second = [] at secondEq
  subst second
  simp [TM2.step, program, clearSecondCfg, clearProcessedCfg, cfg, tapes]

theorem step_clearSecond_cons {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (data : TapeData Data) (tail : List Unit)
    (secondEq : data.second = () :: tail) :
    TM2.step
        (program firstSelected secondSelected positionSelected recipes ending)
        (clearSecondCfg data) =
      some (clearSecondCfg { data with second := tail }) := by
  rcases data with
    ⟨input, first, second, remaining, processed, scratch,
      outputReverse, output⟩
  change second = () :: tail at secondEq
  subst second
  simp [TM2.step, program, clearSecondCfg, cfg, tapes]

theorem step_clearProcessed_nil {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (data : TapeData Data) (processedEq : data.processed = []) :
    TM2.step
        (program firstSelected secondSelected positionSelected recipes ending)
        (clearProcessedCfg data) =
      some (reverseOutputCfg { data with processed := [] }) := by
  rcases data with
    ⟨input, first, second, remaining, processed, scratch,
      outputReverse, output⟩
  change processed = [] at processedEq
  subst processed
  simp [TM2.step, program, clearProcessedCfg, reverseOutputCfg, cfg, tapes]

theorem step_clearProcessed_cons {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (data : TapeData Data) (tail : List Unit)
    (processedEq : data.processed = () :: tail) :
    TM2.step
        (program firstSelected secondSelected positionSelected recipes ending)
        (clearProcessedCfg data) =
      some (clearProcessedCfg { data with processed := tail }) := by
  rcases data with
    ⟨input, first, second, remaining, processed, scratch,
      outputReverse, output⟩
  change processed = () :: tail at processedEq
  subst processed
  simp [TM2.step, program, clearProcessedCfg, cfg, tapes]

theorem step_reverseOutput_nil {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (data : TapeData Data) (outputReverseEq : data.outputReverse = []) :
    TM2.step
        (program firstSelected secondSelected positionSelected recipes ending)
        (reverseOutputCfg data) =
      some (haltDataCfg { data with outputReverse := [] }) := by
  rcases data with
    ⟨input, first, second, remaining, processed, scratch,
      outputReverse, output⟩
  change outputReverse = [] at outputReverseEq
  subst outputReverse
  simp [TM2.step, program, reverseOutputCfg, haltDataCfg, cfg, tapes]

theorem step_reverseOutput_cons {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (data : TapeData Data) (workspace : Workspace Data)
    (tail : List (Workspace Data))
    (outputReverseEq : data.outputReverse = workspace :: tail) :
    TM2.step
        (program firstSelected secondSelected positionSelected recipes ending)
        (reverseOutputCfg data) =
      some (reverseOutputCfg
        { data with
          outputReverse := tail
          output := workspace :: data.output }) := by
  rcases data with
    ⟨input, first, second, remaining, processed, scratch,
      outputReverse, output⟩
  change outputReverse = workspace :: tail at outputReverseEq
  subst outputReverse
  rcases workspace with dataValue | token <;>
    simp [TM2.step, program, reverseOutputCfg, cfg, tapes,
      workspaceFromState]

end TrivariateTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
