/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTrivariateTemplateEmitterRecipeRange

/-! # Position-range execution for the trivariate template emitter -/

namespace LeanTrominoes

open StateTransition Turing

namespace PeriodicCNF
namespace TrivariateTemplateEmitterMachine

open UnaryProgramTokens
open TrivariateTemplateEmitter

def positionRangeTime (recipes : List Recipe)
    (first second firstPosition : Nat) : Nat → Nat
  | 0 => 1
  | count + 1 =>
      1 + templateTime recipes first second firstPosition +
        positionRangeTime recipes first second (firstPosition + 1) count

def positions_evalsInTime {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (first second firstPosition count : Nat) (data : TapeData Data)
    (firstEq : data.first = List.replicate first ())
    (secondEq : data.second = List.replicate second ())
    (remainingEq : data.remaining = List.replicate count ())
    (processedEq : data.processed = List.replicate firstPosition ())
    (scratchEq : data.scratch = []) :
    EvalsToInTime
      (TM2.step
        (program firstSelected secondSelected positionSelected recipes ending))
      (beginPositionCfg data)
      (some (emitEndingCfg
        { data with
          first := List.replicate first ()
          second := List.replicate second ()
          remaining := []
          processed := List.replicate (firstPosition + count) ()
          scratch := []
          outputReverse :=
            ((positionRangeTokens recipes first second firstPosition count).map
              fun token => (Sum.inr token : Workspace Data)).reverse ++
                data.outputReverse }))
      (positionRangeTime recipes first second firstPosition count) := by
  induction count generalizing firstPosition data with
  | zero =>
      have step := oneStep
        (step_beginPosition_nil firstSelected secondSelected positionSelected
          recipes ending data (by simpa using remainingEq))
      convert step using 1 <;>
        simp [positionRangeTime, firstEq, secondEq, processedEq, scratchEq]
  | succ count induction =>
      by_cases recipesEmpty : recipes = []
      · have stepRun := oneStep
          (step_beginPosition_cons_empty firstSelected secondSelected
            positionSelected recipes ending recipesEmpty data
            (List.replicate count ()) (by
              simpa [List.replicate_succ] using remainingEq))
        let nextData : TapeData Data :=
          { data with
            remaining := List.replicate count ()
            processed := () :: data.processed }
        have rest := induction (firstPosition + 1) nextData (by
          simpa [nextData] using firstEq) (by
          simpa [nextData] using secondEq) rfl (by
          simpa [nextData, List.replicate_succ] using processedEq) (by
          simpa [nextData] using scratchEq)
        have composed := EvalsToInTime.trans
          (TM2.step
            (program firstSelected secondSelected positionSelected
              recipes ending))
          1 (positionRangeTime recipes first second (firstPosition + 1) count)
          (beginPositionCfg data) (beginPositionCfg nextData)
          (some (emitEndingCfg
            { nextData with
              first := List.replicate first ()
              second := List.replicate second ()
              remaining := []
              processed := List.replicate (firstPosition + 1 + count) ()
              scratch := []
              outputReverse :=
                ((positionRangeTokens recipes first second
                    (firstPosition + 1) count).map fun token =>
                  (Sum.inr token : Workspace Data)).reverse ++
                    nextData.outputReverse }))
          stepRun rest
        convert composed using 1
        · subst recipes
          simp [nextData, positionRangeTokens, positionTokens]
          congr 3
          omega
        · subst recipes
          simp [positionRangeTime, templateTime]
          omega
      · have recipesNonempty : 0 < recipes.length := by
          cases recipes with
          | nil => exact False.elim (recipesEmpty rfl)
          | cons recipe recipes => simp
        let selectedData : TapeData Data :=
          { data with remaining := List.replicate count () }
        have stepRun := oneStep
          (step_beginPosition_cons_nonempty firstSelected secondSelected
            positionSelected recipes ending recipesNonempty data
            (List.replicate count ()) (by
              simpa [List.replicate_succ] using remainingEq))
        have templateRun := executeRecipes_evalsInTime firstSelected
          secondSelected positionSelected recipes ending
          ⟨0, recipesNonempty⟩ first second firstPosition selectedData (by
            simpa [selectedData] using firstEq) (by
            simpa [selectedData] using secondEq) (by
            simpa [selectedData] using processedEq) (by
            simpa [selectedData] using scratchEq)
        let emittedData : TapeData Data :=
          { selectedData with
            first := List.replicate first ()
            second := List.replicate second ()
            processed := () :: List.replicate firstPosition ()
            scratch := []
            outputReverse :=
              ((positionTokens recipes first second firstPosition).map
                fun token =>
                  (Sum.inr token : Workspace Data)).reverse ++
                    selectedData.outputReverse }
        have firstTwo := EvalsToInTime.trans
          (TM2.step
            (program firstSelected secondSelected positionSelected
              recipes ending))
          1 (templateTime recipes first second firstPosition)
          (beginPositionCfg data)
          (executeCfg ⟨0, recipesNonempty⟩ selectedData)
          (some (beginPositionCfg emittedData)) stepRun (by
            simpa [emittedData] using templateRun)
        have rest := induction (firstPosition + 1) emittedData rfl rfl rfl (by
          simp [emittedData, List.replicate_succ]) rfl
        have composed := EvalsToInTime.trans
          (TM2.step
            (program firstSelected secondSelected positionSelected
              recipes ending))
          (templateTime recipes first second firstPosition + 1)
          (positionRangeTime recipes first second (firstPosition + 1) count)
          (beginPositionCfg data) (beginPositionCfg emittedData)
          (some (emitEndingCfg
            { emittedData with
              first := List.replicate first ()
              second := List.replicate second ()
              remaining := []
              processed := List.replicate (firstPosition + 1 + count) ()
              scratch := []
              outputReverse :=
                ((positionRangeTokens recipes first second
                    (firstPosition + 1) count).map fun token =>
                  (Sum.inr token : Workspace Data)).reverse ++
                    emittedData.outputReverse }))
          firstTwo rest
        convert composed using 1
        · simp [emittedData, selectedData, positionRangeTokens_succ,
            List.map_append, List.reverse_append, List.append_assoc]
          congr 3
          omega
        · simp [positionRangeTime]
          omega

end TrivariateTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
