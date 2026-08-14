/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTriangularTemplateEmitterOuterCounter

/-!
# Inner-position counter execution of the triangular emitter

Inner equality templates scan the already processed higher-position markers
after the persistent and outer counters.  This file verifies their exact
second-stride output, restoration, and continuation to the next inner recipe
or completed inner position.
-/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF
namespace TriangularTemplateEmitterMachine

open UnaryProgramTokens

namespace Parameters

def restoreInnerCfg {Data : Type} (parameters : Parameters Data)
    (index : Fin parameters.inner.length) (data : TapeData Data) :=
  TriangularTemplateEmitterMachine.restoreInnerCfg
    (outerFirst := parameters.outerFirst) (inner := parameters.inner)
    (outerSecond := parameters.outerSecond) index data

end Parameters

theorem step_scanInner_nil {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (index : Fin parameters.inner.length)
    (data : TapeData Data) (innerEq : data.innerProcessed = []) :
    parameters.transition (parameters.scanInnerCfg index data) =
      some (parameters.restoreInnerCfg index
        { data with innerProcessed := [] }) := by
  cases parameters
  cases data
  simp_all [Parameters.transition, Parameters.scanInnerCfg,
      Parameters.restoreInnerCfg, TM2.step, program, scanInner,
      TriangularTemplateEmitterMachine.scanInnerCfg,
      TriangularTemplateEmitterMachine.restoreInnerCfg, cfg, tapes]

theorem step_scanInner_cons_atom {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (index : Fin parameters.inner.length)
    (base firstStride secondStride : Nat) (data : TapeData Data)
    (tail : List Unit) (innerEq : data.innerProcessed = () :: tail)
    (recipeEq : parameters.inner.get index =
      .atom base firstStride secondStride) :
    parameters.transition (parameters.scanInnerCfg index data) =
      some (parameters.scanInnerCfg index
        { data with
          innerProcessed := tail
          positionScratch := () :: data.positionScratch
          outputReverse :=
            List.replicate secondStride
                (Sum.inr Token.atomUnit : Workspace Data) ++
              data.outputReverse }) := by
  cases parameters
  cases data
  simp_all [Parameters.transition, Parameters.scanInnerCfg, TM2.step,
      program, scanInner, TriangularTemplateEmitterMachine.scanInnerCfg,
      cfg, tapes, stepAux_pushAtomUnits]

theorem step_restoreInner_cons {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (index : Fin parameters.inner.length)
    (data : TapeData Data) (tail : List Unit)
    (scratchEq : data.positionScratch = () :: tail) :
    parameters.transition (parameters.restoreInnerCfg index data) =
      some (parameters.restoreInnerCfg index
        { data with
          innerProcessed := () :: data.innerProcessed
          positionScratch := tail }) := by
  cases parameters
  cases data
  simp_all [Parameters.transition, Parameters.restoreInnerCfg, TM2.step,
      program, restoreInner,
      TriangularTemplateEmitterMachine.restoreInnerCfg, cfg, tapes]

theorem step_restoreInner_nil {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (index : Fin parameters.inner.length)
    (data : TapeData Data) (scratchEq : data.positionScratch = []) :
    parameters.transition (parameters.restoreInnerCfg index data) =
      some (parameters.afterRecipeCfg .inner index
        { data with positionScratch := [] }) := by
  cases parameters
  cases data
  simp_all [Parameters.transition, Parameters.restoreInnerCfg,
      Parameters.afterRecipeCfg, Parameters.executeCfg, TM2.step, program,
      restoreInner, afterRecipe,
      TriangularTemplateEmitterMachine.restoreInnerCfg,
      TriangularTemplateEmitterMachine.executeCfg, cfg, tapes,
      stageLabel, afterStage]
  all_goals
    split <;> simp_all [TM2.stepAux]

/-- Scan the processed-inner counter and emit its second-stride contribution. -/
def scanInner_evalsInTime {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (index : Fin parameters.inner.length)
    (base firstStride secondStride : Nat)
    (recipeEq : parameters.inner.get index =
      .atom base firstStride secondStride)
    (word : List Unit) (data : TapeData Data)
    (innerEq : data.innerProcessed = word) :
    EvalsToInTime parameters.transition
      (parameters.scanInnerCfg index data)
      (some (parameters.restoreInnerCfg index
        { data with
          innerProcessed := []
          positionScratch := word.reverse ++ data.positionScratch
          outputReverse :=
            List.replicate (secondStride * word.length)
                (Sum.inr Token.atomUnit : Workspace Data) ++
              data.outputReverse }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_scanInner_nil parameters index data innerEq)
      convert step using 1 <;> simp
  | cons element word induction =>
      have elementEq : element = () := Subsingleton.elim _ _
      subst element
      let nextData : TapeData Data :=
        { data with
          innerProcessed := word
          positionScratch := () :: data.positionScratch
          outputReverse :=
            List.replicate secondStride
                (Sum.inr Token.atomUnit : Workspace Data) ++
              data.outputReverse }
      have firstStep := oneStep
        (step_scanInner_cons_atom parameters index base firstStride
          secondStride data word innerEq recipeEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans parameters.transition
        1 (word.length + 1)
        (parameters.scanInnerCfg index data)
        (parameters.scanInnerCfg index nextData)
        (some (parameters.restoreInnerCfg index
          { nextData with
            innerProcessed := []
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

/-- Restore the processed-inner counter and advance the inner recipe. -/
def restoreInner_evalsInTime {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (index : Fin parameters.inner.length)
    (word : List Unit) (data : TapeData Data)
    (scratchEq : data.positionScratch = word) :
    EvalsToInTime parameters.transition
      (parameters.restoreInnerCfg index data)
      (some (parameters.afterRecipeCfg .inner index
        { data with
          innerProcessed := word.reverse ++ data.innerProcessed
          positionScratch := [] }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_restoreInner_nil parameters index data scratchEq)
      convert step using 1 <;> simp
  | cons element word induction =>
      have elementEq : element = () := Subsingleton.elim _ _
      subst element
      let nextData : TapeData Data :=
        { data with
          innerProcessed := () :: data.innerProcessed
          positionScratch := word }
      have firstStep := oneStep
        (step_restoreInner_cons parameters index data word scratchEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans parameters.transition
        1 (word.length + 1)
        (parameters.restoreInnerCfg index data)
        (parameters.restoreInnerCfg index nextData)
        (some (parameters.afterRecipeCfg .inner index
          { nextData with
            innerProcessed := word.reverse ++ nextData.innerProcessed
            positionScratch := [] }))
        firstStep rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

end TriangularTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
