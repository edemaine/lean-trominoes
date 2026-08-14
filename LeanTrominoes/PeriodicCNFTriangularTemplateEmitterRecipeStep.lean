/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTriangularTemplateEmitterInnerCounter

/-!
# Recipe-entry steps of the triangular template emitter

Fixed recipes append their literal token and advance immediately.  Atom
recipes append their base run and enter the already verified first-, outer-,
and inner-counter pipeline.
-/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF
namespace TriangularTemplateEmitterMachine

open UnaryProgramTokens

theorem step_execute_fixed {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (stage : Stage)
    (index : Fin (stageCount parameters.outerFirst parameters.inner
      parameters.outerSecond stage)) (token : Token) (data : TapeData Data)
    (recipeEq : recipeAt parameters.outerFirst parameters.inner
      parameters.outerSecond stage index = .fixed token) :
    parameters.transition (parameters.executeCfg stage index data) =
      some (parameters.afterRecipeCfg stage index
        { data with
          outputReverse :=
            (Sum.inr token : Workspace Data) :: data.outputReverse }) := by
  cases stage <;> cases parameters <;> cases data <;>
    simp_all [Parameters.transition, Parameters.executeCfg,
      Parameters.afterRecipeCfg, TM2.step, program, executeRecipe,
      afterRecipe, TriangularTemplateEmitterMachine.executeCfg, cfg,
      stageLabel, afterStage, stepAux_pushTokens]
  all_goals
    split <;> simp_all [TM2.stepAux]

theorem step_execute_atom {Data : Type} [Inhabited Data]
    (parameters : Parameters Data) (stage : Stage)
    (index : Fin (stageCount parameters.outerFirst parameters.inner
      parameters.outerSecond stage))
    (base firstStride secondStride : Nat) (data : TapeData Data)
    (recipeEq : recipeAt parameters.outerFirst parameters.inner
      parameters.outerSecond stage index =
        .atom base firstStride secondStride) :
    parameters.transition (parameters.executeCfg stage index data) =
      some (parameters.scanFirstCfg stage index
        { data with
          outputReverse :=
            List.replicate base
                (Sum.inr Token.atomUnit : Workspace Data) ++
              data.outputReverse }) := by
  cases stage <;> cases parameters <;> cases data <;>
    simp_all [Parameters.transition, Parameters.executeCfg,
      Parameters.scanFirstCfg, TM2.step, program, executeRecipe,
      TriangularTemplateEmitterMachine.executeCfg,
      TriangularTemplateEmitterMachine.scanFirstCfg, cfg,
      stageLabel, scanFirstLabel, stepAux_pushAtomUnits]

end TriangularTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
