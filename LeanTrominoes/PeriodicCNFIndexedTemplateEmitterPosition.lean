/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIndexedTemplateEmitterRecipeStep

/-!
# Indexed template emitter position rescan

Exact atom-stride scanning and restoration of the unary processed-position
counter.
-/

namespace LeanTrominoes

open StateTransition Turing

namespace PeriodicCNF
namespace IndexedTemplateEmitterMachine

open AffineTemplateEmitterMachine
open IndexedTemplateEmitter
open UnaryProgramTokens

theorem step_scanPosition_nil {Data : Type} [Inhabited Data]
    (family : Family Data) (item : Data)
    (index : Fin (recipesFor family item).length) (data : TapeData Data)
    (processedEq : data.processed = []) :
    TM2.step (program family) (scanPositionCfg item index data) =
      some (restorePositionCfg item index { data with processed := [] }) := by
  rcases data with
    ⟨input, inputReverse, processed, scratch, tokenReverse, output⟩
  change processed = [] at processedEq
  subst processed
  simp [TM2.step, program, scanPositionCfg, restorePositionCfg, cfg, tapes]

theorem step_scanPosition_cons_atom {Data : Type} [Inhabited Data]
    (family : Family Data) (item : Data)
    (index : Fin (recipesFor family item).length) (base stride : Nat)
    (data : TapeData Data) (tail : List Unit)
    (processedEq : data.processed = () :: tail)
    (recipeEq : (recipesFor family item).get index = .atom base stride) :
    TM2.step (program family) (scanPositionCfg item index data) =
      some (scanPositionCfg item index
        { data with
          processed := tail
          scratch := () :: data.scratch
          tokenReverse :=
            List.replicate stride Token.atomUnit ++ data.tokenReverse }) := by
  rcases data with
    ⟨input, inputReverse, processed, scratch, tokenReverse, output⟩
  change processed = () :: tail at processedEq
  subst processed
  simp only [TM2.step, program, scanPositionCfg, cfg]
  rw [recipeEq]
  simp only [TM2.stepAux, update_tapes_processed, update_tapes_scratch]
  rw [stepAux_pushAtomUnits]
  rfl

theorem step_restorePosition_nil {Data : Type} [Inhabited Data]
    (family : Family Data) (item : Data)
    (index : Fin (recipesFor family item).length) (data : TapeData Data)
    (scratchEq : data.scratch = []) :
    TM2.step (program family) (restorePositionCfg item index data) =
      some (afterRecipeCfg family item index { data with scratch := [] }) := by
  rcases data with
    ⟨input, inputReverse, processed, scratch, tokenReverse, output⟩
  change scratch = [] at scratchEq
  subst scratch
  by_cases nextExists : index.val + 1 < (recipesFor family item).length
  · simp [TM2.step, program, restorePositionCfg, afterRecipe,
      afterRecipeCfg, nextExists, executeCfg, cfg, tapes]
  · simp [TM2.step, program, restorePositionCfg, afterRecipe,
      afterRecipeCfg, nextExists, scanCfg, cfg, tapes]

theorem step_restorePosition_cons {Data : Type} [Inhabited Data]
    (family : Family Data) (item : Data)
    (index : Fin (recipesFor family item).length) (data : TapeData Data)
    (tail : List Unit) (scratchEq : data.scratch = () :: tail) :
    TM2.step (program family) (restorePositionCfg item index data) =
      some (restorePositionCfg item index
        { data with
          processed := () :: data.processed
          scratch := tail }) := by
  rcases data with
    ⟨input, inputReverse, processed, scratch, tokenReverse, output⟩
  change scratch = () :: tail at scratchEq
  subst scratch
  simp [TM2.step, program, restorePositionCfg, cfg, tapes]

end IndexedTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
