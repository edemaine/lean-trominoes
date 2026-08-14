/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTriangularTemplateEmitterScan

/-!
# Persistent-counter execution of the triangular emitter

Every affine atom rescans and restores the persistent first counter.  Inner
templates additionally account for the currently held outer marker, adding
one copy of the atom's second stride before the ordinary processed-position
scan begins.
-/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF
namespace TriangularTemplateEmitterMachine

open UnaryProgramTokens

namespace Parameters

def scanFirstCfg {Data : Type} (parameters : Parameters Data)
    (stage : Stage)
    (index : Fin (stageCount parameters.outerFirst parameters.inner
      parameters.outerSecond stage)) (data : TapeData Data) :=
  TriangularTemplateEmitterMachine.scanFirstCfg parameters.outerFirst
    parameters.inner parameters.outerSecond stage index data

def restoreFirstCfg {Data : Type} (parameters : Parameters Data)
    (stage : Stage)
    (index : Fin (stageCount parameters.outerFirst parameters.inner
      parameters.outerSecond stage)) (data : TapeData Data) :=
  TriangularTemplateEmitterMachine.restoreFirstCfg parameters.outerFirst
    parameters.inner parameters.outerSecond stage index data

def scanPositionCfg {Data : Type} (parameters : Parameters Data)
    (stage : Stage)
    (index : Fin (stageCount parameters.outerFirst parameters.inner
      parameters.outerSecond stage)) (data : TapeData Data) :=
  TriangularTemplateEmitterMachine.scanPositionCfg parameters.outerFirst
    parameters.inner parameters.outerSecond stage index data

end Parameters

/-- Second-stride contribution of the held current marker.  It is present
only while executing the inner equality template. -/
def heldOffset {Data : Type} (parameters : Parameters Data) (stage : Stage)
    (index : Fin (stageCount parameters.outerFirst parameters.inner
      parameters.outerSecond stage)) : Nat :=
  if stage.isInner then
    match recipeAt parameters.outerFirst parameters.inner
        parameters.outerSecond stage index with
    | .fixed _ => 0
    | .atom _ _ secondStride => secondStride
  else 0

theorem step_scanFirst_nil {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (stage : Stage)
    (index : Fin (stageCount parameters.outerFirst parameters.inner
      parameters.outerSecond stage)) (data : TapeData Data)
    (firstEq : data.first = []) :
    parameters.transition (parameters.scanFirstCfg stage index data) =
      some (parameters.restoreFirstCfg stage index
        { data with first := [] }) := by
  cases stage <;> cases parameters <;> cases data <;>
    simp_all [Parameters.transition, Parameters.scanFirstCfg,
      Parameters.restoreFirstCfg, TM2.step, program, scanFirst,
      TriangularTemplateEmitterMachine.scanFirstCfg,
      TriangularTemplateEmitterMachine.restoreFirstCfg, cfg, tapes,
      scanFirstLabel, restoreFirstLabel]

theorem step_scanFirst_cons_atom {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (stage : Stage)
    (index : Fin (stageCount parameters.outerFirst parameters.inner
      parameters.outerSecond stage))
    (base firstStride secondStride : Nat) (data : TapeData Data)
    (tail : List Unit) (firstEq : data.first = () :: tail)
    (recipeEq : recipeAt parameters.outerFirst parameters.inner
      parameters.outerSecond stage index =
        .atom base firstStride secondStride) :
    parameters.transition (parameters.scanFirstCfg stage index data) =
      some (parameters.scanFirstCfg stage index
        { data with
          first := tail
          firstScratch := () :: data.firstScratch
          outputReverse :=
            List.replicate firstStride
                (Sum.inr Token.atomUnit : Workspace Data) ++
              data.outputReverse }) := by
  cases stage <;> cases parameters <;> cases data <;>
    simp_all [Parameters.transition, Parameters.scanFirstCfg, TM2.step,
      program, scanFirst, TriangularTemplateEmitterMachine.scanFirstCfg,
      cfg, tapes, scanFirstLabel, stepAux_pushAtomUnits]

theorem step_restoreFirst_nil {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (stage : Stage)
    (index : Fin (stageCount parameters.outerFirst parameters.inner
      parameters.outerSecond stage)) (data : TapeData Data)
    (scratchEq : data.firstScratch = []) :
    parameters.transition (parameters.restoreFirstCfg stage index data) =
      some (parameters.scanPositionCfg stage index
        { data with
          firstScratch := []
          outputReverse :=
            List.replicate (heldOffset parameters stage index)
                (Sum.inr Token.atomUnit : Workspace Data) ++
              data.outputReverse }) := by
  cases stage <;> cases parameters <;> cases data <;>
    simp_all [Parameters.transition, Parameters.restoreFirstCfg,
      Parameters.scanPositionCfg, heldOffset, TM2.step, program,
      restoreFirst, TriangularTemplateEmitterMachine.restoreFirstCfg,
      TriangularTemplateEmitterMachine.scanPositionCfg, cfg, tapes,
      restoreFirstLabel, scanPositionLabel,
      stepAux_pushAtomUnits]
  rfl

theorem step_restoreFirst_cons {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (stage : Stage)
    (index : Fin (stageCount parameters.outerFirst parameters.inner
      parameters.outerSecond stage)) (data : TapeData Data)
    (tail : List Unit) (scratchEq : data.firstScratch = () :: tail) :
    parameters.transition (parameters.restoreFirstCfg stage index data) =
      some (parameters.restoreFirstCfg stage index
        { data with
          first := () :: data.first
          firstScratch := tail }) := by
  cases stage <;> cases parameters <;> cases data <;>
    simp_all [Parameters.transition, Parameters.restoreFirstCfg, TM2.step,
      program, restoreFirst,
      TriangularTemplateEmitterMachine.restoreFirstCfg, cfg, tapes,
      restoreFirstLabel]

/-- Complete persistent-counter scan for one atom recipe. -/
def scanFirst_evalsInTime {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (stage : Stage)
    (index : Fin (stageCount parameters.outerFirst parameters.inner
      parameters.outerSecond stage))
    (base firstStride secondStride : Nat)
    (recipeEq : recipeAt parameters.outerFirst parameters.inner
      parameters.outerSecond stage index =
        .atom base firstStride secondStride)
    (word : List Unit) (data : TapeData Data)
    (firstEq : data.first = word) :
    EvalsToInTime parameters.transition
      (parameters.scanFirstCfg stage index data)
      (some (parameters.restoreFirstCfg stage index
        { data with
          first := []
          firstScratch := word.reverse ++ data.firstScratch
          outputReverse :=
            List.replicate (firstStride * word.length)
                (Sum.inr Token.atomUnit : Workspace Data) ++
              data.outputReverse }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_scanFirst_nil parameters stage index data firstEq)
      convert step using 1 <;> simp
  | cons element word induction =>
      have elementEq : element = () := Subsingleton.elim _ _
      subst element
      let nextData : TapeData Data :=
        { data with
          first := word
          firstScratch := () :: data.firstScratch
          outputReverse :=
            List.replicate firstStride
                (Sum.inr Token.atomUnit : Workspace Data) ++
              data.outputReverse }
      have firstStep := oneStep
        (step_scanFirst_cons_atom parameters stage index base firstStride
          secondStride data word firstEq recipeEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans parameters.transition
        1 (word.length + 1)
        (parameters.scanFirstCfg stage index data)
        (parameters.scanFirstCfg stage index nextData)
        (some (parameters.restoreFirstCfg stage index
          { nextData with
            first := []
            firstScratch := word.reverse ++ nextData.firstScratch
            outputReverse :=
              List.replicate (firstStride * word.length)
                  (Sum.inr Token.atomUnit : Workspace Data) ++
                nextData.outputReverse }))
        firstStep rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
        rw [show firstStride * (word.length + 1) =
            firstStride * word.length + firstStride by ring,
          List.replicate_add, List.append_assoc]
      · simp

/-- Restore the persistent counter and account for the held inner offset. -/
def restoreFirst_evalsInTime {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (stage : Stage)
    (index : Fin (stageCount parameters.outerFirst parameters.inner
      parameters.outerSecond stage))
    (word : List Unit) (data : TapeData Data)
    (scratchEq : data.firstScratch = word) :
    EvalsToInTime parameters.transition
      (parameters.restoreFirstCfg stage index data)
      (some (parameters.scanPositionCfg stage index
        { data with
          first := word.reverse ++ data.first
          firstScratch := []
          outputReverse :=
            List.replicate (heldOffset parameters stage index)
                (Sum.inr Token.atomUnit : Workspace Data) ++
              data.outputReverse }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_restoreFirst_nil parameters stage index data scratchEq)
      convert step using 1 <;> simp
  | cons element word induction =>
      have elementEq : element = () := Subsingleton.elim _ _
      subst element
      let nextData : TapeData Data :=
        { data with
          first := () :: data.first
          firstScratch := word }
      have firstStep := oneStep
        (step_restoreFirst_cons parameters stage index data word scratchEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans parameters.transition
        1 (word.length + 1)
        (parameters.restoreFirstCfg stage index data)
        (parameters.restoreFirstCfg stage index nextData)
        (some (parameters.scanPositionCfg stage index
          { nextData with
            first := word.reverse ++ nextData.first
            firstScratch := []
            outputReverse :=
              List.replicate (heldOffset parameters stage index)
                  (Sum.inr Token.atomUnit : Workspace Data) ++
                nextData.outputReverse }))
        firstStep rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

end TriangularTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
