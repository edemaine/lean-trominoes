/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIndexedTemplateEmitterConfigurations

/-!
# Indexed template emitter scan steps

Exact one-step behavior for retaining each input item and dispatching its
optional data-dependent recipe.  Empty selected recipes still advance the
processed-position counter; unselected items do not.
-/

namespace LeanTrominoes

open StateTransition Turing

namespace PeriodicCNF
namespace IndexedTemplateEmitterMachine

open IndexedTemplateEmitter

theorem step_scan_nil {Data : Type} [Inhabited Data]
    (family : Family Data) (data : TapeData Data)
    (inputEq : data.input = []) :
    TM2.step (program family) (scanCfg data) =
      some (clearProcessedCfg { data with input := [] }) := by
  rcases data with
    ⟨input, inputReverse, processed, scratch, tokenReverse, output⟩
  change input = [] at inputEq
  subst input
  simp [TM2.step, program, scanCfg, clearProcessedCfg, cfg, tapes]

theorem step_scan_cons {Data : Type} [Inhabited Data]
    (family : Family Data) (data : TapeData Data) (item : Data)
    (tail : List Data) (inputEq : data.input = item :: tail) :
    TM2.step (program family) (scanCfg data) =
      some (beginItemCfg item
        { data with
          input := tail
          inputReverse := item :: data.inputReverse }) := by
  rcases data with
    ⟨input, inputReverse, processed, scratch, tokenReverse, output⟩
  change input = item :: tail at inputEq
  subst input
  simp [TM2.step, program, scanCfg, beginItemCfg, cfg, tapes,
    dataFromState]

theorem step_beginItem_none {Data : Type} [Inhabited Data]
    (family : Family Data) (item : Data) (data : TapeData Data)
    (none : family item = none) :
    TM2.step (program family) (beginItemCfg item data) =
      some (scanCfg (family := family) data) := by
  simp only [TM2.step, beginItemCfg, cfg]
  rw [program]
  split <;> simp_all [scanCfg, cfg]

theorem step_beginItem_some_nonempty {Data : Type} [Inhabited Data]
    (family : Family Data) (item : Data) (recipes : List
      AffineTemplateEmitterMachine.Recipe) (data : TapeData Data)
    (value : family item = some recipes) (nonempty : 0 < recipes.length) :
    let indexedNonempty : 0 < (recipesFor family item).length := by
      simpa [recipesFor, value] using nonempty
    TM2.step (program family) (beginItemCfg item data) =
      some (executeCfg item ⟨0, indexedNonempty⟩ data) := by
  dsimp only
  simp only [TM2.step, beginItemCfg, cfg]
  rw [program]
  split
  · simp_all
  · rename_i recipes' equation
    have recipesEq : recipes' = recipes :=
      Option.some.inj (equation.symm.trans value)
    subst recipes'
    simp [nonempty, recipesFor, executeCfg, cfg]

theorem step_beginItem_some_empty {Data : Type} [Inhabited Data]
    (family : Family Data) (item : Data) (recipes : List
      AffineTemplateEmitterMachine.Recipe) (data : TapeData Data)
    (value : family item = some recipes) (empty : recipes.length = 0) :
    TM2.step (program family) (beginItemCfg item data) =
      some (scanCfg (family := family)
        { data with processed := () :: data.processed }) := by
  simp only [TM2.step, beginItemCfg, cfg]
  rw [program]
  split
  · simp_all
  · rename_i recipes' equation
    have recipesEq : recipes' = recipes :=
      Option.some.inj (equation.symm.trans value)
    subst recipes'
    simp [empty, scanCfg, cfg, tapes]

end IndexedTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
