/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIndexedTemplateEmitterScan

/-!
# Indexed template emitter recipe entry

Token-push algebra and exact entry steps for fixed and affine-atom recipes.
-/

namespace LeanTrominoes

open StateTransition Turing

namespace PeriodicCNF
namespace IndexedTemplateEmitterMachine

open AffineTemplateEmitterMachine
open IndexedTemplateEmitter
open UnaryProgramTokens

theorem stepAux_pushTokens {Data : Type} {family : Family Data}
    (tokens : List Token)
    (next : TM2.Stmt (Alphabet Data) (Label Data family) (State Data))
    (state : State Data) (data : TapeData Data) :
    TM2.stepAux (pushTokens tokens next) state (tapes data) =
      TM2.stepAux next state
        (tapes { data with
          tokenReverse := tokens.reverse ++ data.tokenReverse }) := by
  induction tokens generalizing data with
  | nil => simp [pushTokens]
  | cons token tokens induction =>
      simp only [pushTokens, List.foldr_cons, TM2.stepAux]
      rw [update_tapes_tokenReverse]
      change TM2.stepAux (pushTokens tokens next) state
          (tapes { data with
            tokenReverse := token :: data.tokenReverse }) = _
      rw [induction]
      simp [List.reverse_cons, List.append_assoc]

theorem stepAux_pushAtomUnits {Data : Type} {family : Family Data}
    (count : Nat)
    (next : TM2.Stmt (Alphabet Data) (Label Data family) (State Data))
    (state : State Data) (data : TapeData Data) :
    TM2.stepAux (pushAtomUnits count next) state (tapes data) =
      TM2.stepAux next state
        (tapes { data with
          tokenReverse :=
            List.replicate count Token.atomUnit ++ data.tokenReverse }) := by
  rw [pushAtomUnits, stepAux_pushTokens]
  simp

theorem step_execute_fixed {Data : Type} [Inhabited Data]
    (family : Family Data) (item : Data)
    (index : Fin (recipesFor family item).length) (token : Token)
    (data : TapeData Data)
    (recipeEq : (recipesFor family item).get index = .fixed token) :
    TM2.step (program family) (executeCfg item index data) =
      some (afterRecipeCfg family item index
        { data with tokenReverse := token :: data.tokenReverse }) := by
  simp only [TM2.step, program, executeCfg, cfg]
  rw [recipeEq]
  by_cases nextExists : index.val + 1 < (recipesFor family item).length
  · simp [afterRecipe, afterRecipeCfg, nextExists, executeCfg, cfg, tapes]
  · simp [afterRecipe, afterRecipeCfg, nextExists, scanCfg, cfg, tapes]

theorem step_execute_atom {Data : Type} [Inhabited Data]
    (family : Family Data) (item : Data)
    (index : Fin (recipesFor family item).length) (base stride : Nat)
    (data : TapeData Data)
    (recipeEq : (recipesFor family item).get index = .atom base stride) :
    TM2.step (program family) (executeCfg item index data) =
      some (scanPositionCfg item index
        { data with
          tokenReverse :=
            List.replicate base Token.atomUnit ++ data.tokenReverse }) := by
  simp only [TM2.step, program, executeCfg, scanPositionCfg, cfg]
  rw [recipeEq, stepAux_pushAtomUnits]
  rfl

end IndexedTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
