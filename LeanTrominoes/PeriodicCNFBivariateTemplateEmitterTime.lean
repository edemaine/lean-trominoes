/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFBivariateTemplateEmitterMachine

/-!
# Polynomial runtime of the bivariate affine-position template emitter

This file keeps the quantitative proof separate from the finite-machine
execution proof.  For a fixed recipe list, both the emitted unary word and the
verified execution time are quadratic in the retained workspace length.
-/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF
namespace BivariateTemplateEmitterMachine

namespace Recipe

/-- Fixed coefficient bounding the token output of one recipe. -/
def weight : Recipe → Nat
  | .fixed _ => 1
  | .atom base firstStride secondStride =>
      base + firstStride + secondStride

theorem tokens_length_le (recipe : Recipe) (first position : Nat) :
    (recipe.tokens first position).length ≤
      recipe.weight * (first + position + 1) := by
  cases recipe with
  | fixed token =>
      simp [BivariateProgramTemplates.Recipe.tokens, weight]
  | atom base firstStride secondStride =>
      simp only [BivariateProgramTemplates.Recipe.tokens,
        List.length_replicate, weight]
      nlinarith

theorem time_le (recipe : Recipe) (first position : Nat) :
    recipeTime first position recipe ≤ 5 * (first + position + 1) := by
  cases recipe <;> simp [recipeTime] <;> omega

end Recipe

/-- Sum of all fixed output coefficients in one position template. -/
def templateWeight (recipes : List Recipe) : Nat :=
  (recipes.map Recipe.weight).sum

theorem positionTokens_length_le (recipes : List Recipe)
    (first position : Nat) :
    (positionTokens recipes first position).length ≤
      templateWeight recipes * (first + position + 1) := by
  induction recipes with
  | nil =>
      simp [positionTokens, BivariateProgramTemplates.positionTokens,
        templateWeight]
  | cons recipe recipes induction =>
      simp only [positionTokens, BivariateProgramTemplates.positionTokens,
        List.flatMap_cons, List.length_append, templateWeight, List.map_cons,
        List.sum_cons]
      have current := Recipe.tokens_length_le recipe first position
      calc
        (BivariateProgramTemplates.Recipe.tokens first position recipe).length +
              (List.flatMap
                (BivariateProgramTemplates.Recipe.tokens first position)
                recipes).length ≤
            recipe.weight * (first + position + 1) +
              templateWeight recipes * (first + position + 1) :=
          Nat.add_le_add current induction
        _ = (recipe.weight + templateWeight recipes) *
              (first + position + 1) := by
          ring

theorem positionRangeTokens_length_le (recipes : List Recipe)
    (first firstPosition count : Nat) :
    (positionRangeTokens recipes first firstPosition count).length ≤
      templateWeight recipes * count *
        (first + firstPosition + count + 1) := by
  induction count generalizing firstPosition with
  | zero => simp
  | succ count induction =>
      rw [positionRangeTokens_succ, List.length_append]
      have current := positionTokens_length_le recipes first firstPosition
      have rest := induction (firstPosition + 1)
      nlinarith

theorem templateTime_le (recipes : List Recipe) (first position : Nat) :
    templateTime recipes first position ≤
      5 * recipes.length * (first + position + 1) := by
  induction recipes with
  | nil => simp [templateTime]
  | cons recipe recipes induction =>
      simp only [templateTime, List.map_cons, List.sum_cons,
        List.length_cons]
      have current := Recipe.time_le recipe first position
      calc
        recipeTime first position recipe +
              (List.map (recipeTime first position) recipes).sum ≤
            5 * (first + position + 1) +
              5 * recipes.length * (first + position + 1) :=
          Nat.add_le_add current induction
        _ = 5 * (recipes.length + 1) *
              (first + position + 1) := by ring

theorem positionRangeTime_le (recipes : List Recipe)
    (first firstPosition count : Nat) :
    positionRangeTime recipes first firstPosition count ≤
      (5 * recipes.length + 2) * (count + 1) *
        (first + firstPosition + count + 1) := by
  induction count generalizing firstPosition with
  | zero =>
      simp [positionRangeTime]
      have positive :
          0 < (5 * recipes.length + 2) *
            (first + firstPosition + 1) :=
        Nat.mul_pos (by omega) (by omega)
      omega
  | succ count induction =>
      rw [positionRangeTime]
      have current := templateTime_le recipes first firstPosition
      have rest := induction (firstPosition + 1)
      nlinarith

theorem selectedCount_le_length {Data : Type} (selected : Data → Bool)
    (workspace : List (Workspace Data)) :
    selectedCount selected workspace ≤ workspace.length := by
  exact UnaryPolynomialPaddingMachine.selectedCount_le_length
    (dataSelected selected) workspace

theorem appendedOutput_length {Data : Type}
    (firstSelected secondSelected : Data → Bool)
    (recipes : List Recipe) (ending : List UnaryProgramTokens.Token)
    (workspace : List (Workspace Data)) :
    (appendedOutput firstSelected secondSelected recipes ending
      workspace).length =
      workspace.length +
        (positionRangeTokens recipes (selectedCount firstSelected workspace) 0
          (selectedCount secondSelected workspace)).length + ending.length := by
  simp [appendedOutput, Nat.add_assoc]

theorem emittedRange_length_le_workspace {Data : Type}
    (firstSelected secondSelected : Data → Bool) (recipes : List Recipe)
    (workspace : List (Workspace Data)) :
    (positionRangeTokens recipes (selectedCount firstSelected workspace) 0
        (selectedCount secondSelected workspace)).length ≤
      2 * templateWeight recipes * (workspace.length + 1) ^ 2 := by
  let first := selectedCount firstSelected workspace
  let count := selectedCount secondSelected workspace
  have firstLe : first ≤ workspace.length :=
    selectedCount_le_length firstSelected workspace
  have countLe : count ≤ workspace.length :=
    selectedCount_le_length secondSelected workspace
  have rangeBound := positionRangeTokens_length_le recipes first 0 count
  have productLe : count * (first + count + 1) ≤
      2 * (workspace.length + 1) ^ 2 := by
    nlinarith
  have weightedLe := Nat.mul_le_mul_left (templateWeight recipes) productLe
  dsimp only [first, count] at rangeBound ⊢
  calc
    _ ≤ templateWeight recipes *
          (2 * (workspace.length + 1) ^ 2) :=
      rangeBound.trans (by simpa [Nat.mul_assoc] using weightedLe)
    _ = _ := by ring

theorem positionRangeTime_le_workspace {Data : Type}
    (firstSelected secondSelected : Data → Bool) (recipes : List Recipe)
    (workspace : List (Workspace Data)) :
    positionRangeTime recipes (selectedCount firstSelected workspace) 0
        (selectedCount secondSelected workspace) ≤
      2 * (5 * recipes.length + 2) * (workspace.length + 1) ^ 2 := by
  let first := selectedCount firstSelected workspace
  let count := selectedCount secondSelected workspace
  have firstLe : first ≤ workspace.length :=
    selectedCount_le_length firstSelected workspace
  have countLe : count ≤ workspace.length :=
    selectedCount_le_length secondSelected workspace
  have rangeBound := positionRangeTime_le recipes first 0 count
  have productLe : (count + 1) * (first + count + 1) ≤
      2 * (workspace.length + 1) ^ 2 := by
    nlinarith
  have weightedLe :=
    Nat.mul_le_mul_left (5 * recipes.length + 2) productLe
  dsimp only [first, count] at rangeBound ⊢
  calc
    _ ≤ (5 * recipes.length + 2) *
          (2 * (workspace.length + 1) ^ 2) :=
      rangeBound.trans (by simpa [Nat.mul_assoc] using weightedLe)
    _ = _ := by ring

/-- A fixed quadratic bound for one fixed bivariate affine template stage. -/
noncomputable def timePolynomial (recipes : List Recipe)
    (ending : List UnaryProgramTokens.Token) : Polynomial Nat :=
  Polynomial.C
      (2 * templateWeight recipes + 10 * recipes.length +
        ending.length + 9) *
    (Polynomial.X + Polynomial.C 1) ^ 2

@[simp]
theorem timePolynomial_eval (recipes : List Recipe)
    (ending : List UnaryProgramTokens.Token) (length : Nat) :
    (timePolynomial recipes ending).eval length =
      (2 * templateWeight recipes + 10 * recipes.length +
        ending.length + 9) *
        (length + 1) ^ 2 := by
  simp [timePolynomial, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_pow]

theorem totalTime_le_polynomial_eval {Data : Type}
    (firstSelected secondSelected : Data → Bool) (recipes : List Recipe)
    (ending : List UnaryProgramTokens.Token)
    (workspace : List (Workspace Data)) :
    totalTime firstSelected secondSelected recipes ending workspace ≤
      (timePolynomial recipes ending).eval workspace.length := by
  rw [timePolynomial_eval]
  have firstCountBound := selectedCount_le_length firstSelected workspace
  have secondCountBound := selectedCount_le_length secondSelected workspace
  have rangeTimeBound :=
    positionRangeTime_le_workspace firstSelected secondSelected recipes
      workspace
  have emittedBound :=
    emittedRange_length_le_workspace firstSelected secondSelected recipes
      workspace
  unfold totalTime
  rw [appendedOutput_length]
  have squareOne : 1 ≤ (workspace.length + 1) ^ 2 := by
    nlinarith
  have endingBound : ending.length ≤
      ending.length * (workspace.length + 1) ^ 2 := by
    simpa using Nat.mul_le_mul_left ending.length squareOne
  have linearBound : 4 * workspace.length + 5 ≤
      5 * (workspace.length + 1) ^ 2 := by
    nlinarith
  have remainderBound : 4 * workspace.length + ending.length + 5 ≤
      (ending.length + 5) * (workspace.length + 1) ^ 2 := by
    calc
      4 * workspace.length + ending.length + 5 =
          (4 * workspace.length + 5) + ending.length := by omega
      _ ≤ 5 * (workspace.length + 1) ^ 2 +
          ending.length * (workspace.length + 1) ^ 2 :=
        Nat.add_le_add linearBound endingBound
      _ = (ending.length + 5) * (workspace.length + 1) ^ 2 := by
        ring
  calc
    workspace.length + 1 +
          positionRangeTime recipes (selectedCount firstSelected workspace) 0
            (selectedCount secondSelected workspace) +
          1 + (selectedCount firstSelected workspace + 1) +
          (selectedCount secondSelected workspace + 1) +
          (workspace.length +
            (positionRangeTokens recipes
              (selectedCount firstSelected workspace) 0
              (selectedCount secondSelected workspace)).length +
                ending.length) +
          1 ≤
        (2 * (5 * recipes.length + 2)) *
            (workspace.length + 1) ^ 2 +
          (2 * templateWeight recipes) * (workspace.length + 1) ^ 2 +
          (4 * workspace.length + ending.length + 5) := by omega
    _ ≤ (2 * (5 * recipes.length + 2)) *
            (workspace.length + 1) ^ 2 +
          (2 * templateWeight recipes) * (workspace.length + 1) ^ 2 +
          ((ending.length + 5) * (workspace.length + 1) ^ 2) :=
      Nat.add_le_add_left remainderBound _
    _ = (2 * templateWeight recipes + 10 * recipes.length +
          ending.length + 9) *
          (workspace.length + 1) ^ 2 := by ring

/-- For fixed recipes and ending, bivariate affine template emission is polynomial-time
in the complete retained workspace length. -/
noncomputable def computableInPolyTime {Data : Type} [Fintype Data]
    [Inhabited Data] (firstSelected secondSelected : Data → Bool)
    (recipes : List Recipe)
    (ending : List UnaryProgramTokens.Token) :
    @TM2ComputableInPolyTime
      (List (Workspace Data)) (List (Workspace Data))
      (Workspace Data) (Workspace Data) id id
      (appendedOutput firstSelected secondSelected recipes ending) where
  tm := machine Data firstSelected secondSelected recipes ending
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := timePolynomial recipes ending
  outputsFun workspace := by
    have run := machine_outputsInTime firstSelected secondSelected recipes
      ending workspace
    have run' : TM2OutputsInTime
        (machine Data firstSelected secondSelected recipes ending)
        (List.map (Equiv.refl (Workspace Data)).invFun (id workspace))
        (some (List.map (Equiv.refl (Workspace Data)).invFun
          (id (appendedOutput firstSelected secondSelected recipes ending
            workspace))))
        (totalTime firstSelected secondSelected recipes ending workspace) := by
      simpa only [FiniteBlockTransducer.map_refl_invFun, id_eq] using run
    exact
      { toEvalsTo := run'.toEvalsTo
        steps_le_m := run'.steps_le_m.trans
          (totalTime_le_polynomial_eval firstSelected secondSelected recipes
            ending workspace) }

end BivariateTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
