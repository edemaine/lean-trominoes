/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTriangularTemplateEmitterFirstCounter

/-!
# Outer-position counter execution of the triangular emitter

After restoring the persistent width counter, every atom scans and restores
the completed-outer-position counter.  Outer templates then advance to their
next recipe or stage; inner templates continue to the additional inner-position
counter verified in the next layer.
-/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF
namespace TriangularTemplateEmitterMachine

open UnaryProgramTokens

namespace Parameters

def restorePositionCfg {Data : Type} (parameters : Parameters Data)
    (stage : Stage)
    (index : Fin (stageCount parameters.outerFirst parameters.inner
      parameters.outerSecond stage)) (data : TapeData Data) :=
  TriangularTemplateEmitterMachine.restorePositionCfg parameters.outerFirst
    parameters.inner parameters.outerSecond stage index data

def executeCfg {Data : Type} (parameters : Parameters Data) (stage : Stage)
    (index : Fin (stageCount parameters.outerFirst parameters.inner
      parameters.outerSecond stage)) (data : TapeData Data) :=
  TriangularTemplateEmitterMachine.executeCfg parameters.outerFirst
    parameters.inner parameters.outerSecond stage index data

def afterRecipeCfg {Data : Type} (parameters : Parameters Data)
    (stage : Stage)
    (index : Fin (stageCount parameters.outerFirst parameters.inner
      parameters.outerSecond stage)) (data : TapeData Data) :=
  if nextExists : index.val + 1 <
      stageCount parameters.outerFirst parameters.inner
        parameters.outerSecond stage then
    executeCfg parameters stage ⟨index.val + 1, nextExists⟩ data
  else
    cfg (afterStage parameters.outerFirst parameters.inner
      parameters.outerSecond stage) none data

def scanInnerCfg {Data : Type} (parameters : Parameters Data)
    (index : Fin parameters.inner.length) (data : TapeData Data) :=
  TriangularTemplateEmitterMachine.scanInnerCfg
    (outerFirst := parameters.outerFirst) (inner := parameters.inner)
    (outerSecond := parameters.outerSecond) index data

def afterPositionCfg {Data : Type} (parameters : Parameters Data)
    (stage : Stage)
    (index : Fin (stageCount parameters.outerFirst parameters.inner
      parameters.outerSecond stage)) (data : TapeData Data) :=
  match stage with
  | .outerFirst => afterRecipeCfg parameters .outerFirst index data
  | .inner => scanInnerCfg parameters index data
  | .outerSecond => afterRecipeCfg parameters .outerSecond index data

end Parameters

theorem step_scanPosition_nil {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (stage : Stage)
    (index : Fin (stageCount parameters.outerFirst parameters.inner
      parameters.outerSecond stage)) (data : TapeData Data)
    (processedEq : data.processed = []) :
    parameters.transition (parameters.scanPositionCfg stage index data) =
      some (parameters.restorePositionCfg stage index
        { data with processed := [] }) := by
  cases stage <;> cases parameters <;> cases data <;>
    simp_all [Parameters.transition, Parameters.scanPositionCfg,
      Parameters.restorePositionCfg, TM2.step, program, scanPosition,
      TriangularTemplateEmitterMachine.scanPositionCfg,
      TriangularTemplateEmitterMachine.restorePositionCfg, cfg, tapes,
      scanPositionLabel, restorePositionLabel]

theorem step_scanPosition_cons_atom {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (stage : Stage)
    (index : Fin (stageCount parameters.outerFirst parameters.inner
      parameters.outerSecond stage))
    (base firstStride secondStride : Nat) (data : TapeData Data)
    (tail : List Unit) (processedEq : data.processed = () :: tail)
    (recipeEq : recipeAt parameters.outerFirst parameters.inner
      parameters.outerSecond stage index =
        .atom base firstStride secondStride) :
    parameters.transition (parameters.scanPositionCfg stage index data) =
      some (parameters.scanPositionCfg stage index
        { data with
          processed := tail
          positionScratch := () :: data.positionScratch
          outputReverse :=
            List.replicate secondStride
                (Sum.inr Token.atomUnit : Workspace Data) ++
              data.outputReverse }) := by
  cases stage <;> cases parameters <;> cases data <;>
    simp_all [Parameters.transition, Parameters.scanPositionCfg, TM2.step,
      program, scanPosition,
      TriangularTemplateEmitterMachine.scanPositionCfg, cfg, tapes,
      scanPositionLabel, stepAux_pushAtomUnits]

theorem step_restorePosition_cons {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (stage : Stage)
    (index : Fin (stageCount parameters.outerFirst parameters.inner
      parameters.outerSecond stage)) (data : TapeData Data)
    (tail : List Unit)
    (scratchEq : data.positionScratch = () :: tail) :
    parameters.transition (parameters.restorePositionCfg stage index data) =
      some (parameters.restorePositionCfg stage index
        { data with
          processed := () :: data.processed
          positionScratch := tail }) := by
  cases stage <;> cases parameters <;> cases data <;>
    simp_all [Parameters.transition, Parameters.restorePositionCfg,
      TM2.step, program, restorePosition,
      TriangularTemplateEmitterMachine.restorePositionCfg, cfg, tapes,
      restorePositionLabel]

theorem step_restorePosition_nil {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (stage : Stage)
    (index : Fin (stageCount parameters.outerFirst parameters.inner
      parameters.outerSecond stage)) (data : TapeData Data)
    (scratchEq : data.positionScratch = []) :
    parameters.transition (parameters.restorePositionCfg stage index data) =
      some (parameters.afterPositionCfg stage index
        { data with positionScratch := [] }) := by
  cases stage <;> cases parameters <;> cases data <;>
    simp_all [Parameters.transition, Parameters.restorePositionCfg,
      Parameters.afterPositionCfg, Parameters.afterRecipeCfg,
      Parameters.executeCfg, Parameters.scanInnerCfg, TM2.step, program,
      restorePosition, afterRecipe,
      TriangularTemplateEmitterMachine.restorePositionCfg,
      TriangularTemplateEmitterMachine.executeCfg,
      TriangularTemplateEmitterMachine.scanInnerCfg, cfg, tapes,
      restorePositionLabel, stageLabel, afterStage]
  all_goals
    split <;> simp_all [TM2.stepAux]

/-- Scan the completed-outer counter and emit its second-stride contribution. -/
def scanPosition_evalsInTime {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (stage : Stage)
    (index : Fin (stageCount parameters.outerFirst parameters.inner
      parameters.outerSecond stage))
    (base firstStride secondStride : Nat)
    (recipeEq : recipeAt parameters.outerFirst parameters.inner
      parameters.outerSecond stage index =
        .atom base firstStride secondStride)
    (word : List Unit) (data : TapeData Data)
    (processedEq : data.processed = word) :
    EvalsToInTime parameters.transition
      (parameters.scanPositionCfg stage index data)
      (some (parameters.restorePositionCfg stage index
        { data with
          processed := []
          positionScratch := word.reverse ++ data.positionScratch
          outputReverse :=
            List.replicate (secondStride * word.length)
                (Sum.inr Token.atomUnit : Workspace Data) ++
              data.outputReverse }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_scanPosition_nil parameters stage index data processedEq)
      convert step using 1 <;> simp
  | cons element word induction =>
      have elementEq : element = () := Subsingleton.elim _ _
      subst element
      let nextData : TapeData Data :=
        { data with
          processed := word
          positionScratch := () :: data.positionScratch
          outputReverse :=
            List.replicate secondStride
                (Sum.inr Token.atomUnit : Workspace Data) ++
              data.outputReverse }
      have firstStep := oneStep
        (step_scanPosition_cons_atom parameters stage index base firstStride
          secondStride data word processedEq recipeEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans parameters.transition
        1 (word.length + 1)
        (parameters.scanPositionCfg stage index data)
        (parameters.scanPositionCfg stage index nextData)
        (some (parameters.restorePositionCfg stage index
          { nextData with
            processed := []
            positionScratch := word.reverse ++ nextData.positionScratch
            outputReverse :=
              List.replicate (secondStride * word.length)
                  (Sum.inr Token.atomUnit : Workspace Data) ++
                nextData.outputReverse }))
        firstStep rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
        rw [show secondStride * (word.length + 1) =
            secondStride * word.length + secondStride by ring,
          List.replicate_add, List.append_assoc]
      · simp

/-- Restore the outer-position counter and enter the stage-specific
continuation. -/
def restorePosition_evalsInTime {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (stage : Stage)
    (index : Fin (stageCount parameters.outerFirst parameters.inner
      parameters.outerSecond stage))
    (word : List Unit) (data : TapeData Data)
    (scratchEq : data.positionScratch = word) :
    EvalsToInTime parameters.transition
      (parameters.restorePositionCfg stage index data)
      (some (parameters.afterPositionCfg stage index
        { data with
          processed := word.reverse ++ data.processed
          positionScratch := [] }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_restorePosition_nil parameters stage index data scratchEq)
      convert step using 1 <;> simp
  | cons element word induction =>
      have elementEq : element = () := Subsingleton.elim _ _
      subst element
      let nextData : TapeData Data :=
        { data with
          processed := () :: data.processed
          positionScratch := word }
      have firstStep := oneStep
        (step_restorePosition_cons parameters stage index data word scratchEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans parameters.transition
        1 (word.length + 1)
        (parameters.restorePositionCfg stage index data)
        (parameters.restorePositionCfg stage index nextData)
        (some (parameters.afterPositionCfg stage index
          { nextData with
            processed := word.reverse ++ nextData.processed
            positionScratch := [] }))
        firstStep rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

end TriangularTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
