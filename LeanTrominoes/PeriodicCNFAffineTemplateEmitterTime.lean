/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFAffineTemplateEmitterMachine

/-!
# Polynomial runtime of the affine-position template emitter

This file keeps the quantitative proof separate from the finite-machine
execution proof.  For a fixed recipe list, both the emitted unary word and the
verified execution time are quadratic in the retained workspace length.
-/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF
namespace AffineTemplateEmitterMachine

namespace Recipe

/-- Fixed coefficient bounding the token output of one recipe. -/
def weight : Recipe → Nat
  | .fixed _ => 1
  | .atom base stride => base + stride

theorem tokens_length_le (recipe : Recipe) (position : Nat) :
    (recipe.tokens position).length ≤ recipe.weight * (position + 1) := by
  cases recipe with
  | fixed token => simp [tokens, weight]
  | atom base stride =>
      simp only [tokens, List.length_replicate, weight]
      nlinarith

theorem time_le (recipe : Recipe) (position : Nat) :
    recipeTime position recipe ≤ 3 * (position + 1) := by
  cases recipe <;> simp [recipeTime] <;> omega

end Recipe

/-- Sum of all fixed output coefficients in one position template. -/
def templateWeight (recipes : List Recipe) : Nat :=
  (recipes.map Recipe.weight).sum

theorem positionTokens_length_le (recipes : List Recipe) (position : Nat) :
    (positionTokens recipes position).length ≤
      templateWeight recipes * (position + 1) := by
  induction recipes with
  | nil => simp [positionTokens, templateWeight]
  | cons recipe recipes induction =>
      simp only [positionTokens, List.flatMap_cons, List.length_append,
        templateWeight, List.map_cons, List.sum_cons]
      have current := Recipe.tokens_length_le recipe position
      calc
        (Recipe.tokens position recipe).length +
              (List.flatMap (Recipe.tokens position) recipes).length ≤
            recipe.weight * (position + 1) +
              templateWeight recipes * (position + 1) :=
          Nat.add_le_add current induction
        _ = (recipe.weight + templateWeight recipes) * (position + 1) := by
          ring

theorem positionRangeTokens_length_le (recipes : List Recipe)
    (firstPosition count : Nat) :
    (positionRangeTokens recipes firstPosition count).length ≤
      templateWeight recipes * count * (firstPosition + count + 1) := by
  induction count generalizing firstPosition with
  | zero => simp
  | succ count induction =>
      rw [positionRangeTokens_succ, List.length_append]
      have current := positionTokens_length_le recipes firstPosition
      have rest := induction (firstPosition + 1)
      nlinarith

theorem templateTime_le (recipes : List Recipe) (position : Nat) :
    templateTime recipes position ≤
      3 * recipes.length * (position + 1) := by
  induction recipes with
  | nil => simp [templateTime]
  | cons recipe recipes induction =>
      simp only [templateTime, List.map_cons, List.sum_cons,
        List.length_cons]
      have current := Recipe.time_le recipe position
      calc
        recipeTime position recipe +
              (List.map (recipeTime position) recipes).sum ≤
            3 * (position + 1) +
              3 * recipes.length * (position + 1) :=
          Nat.add_le_add current induction
        _ = 3 * (recipes.length + 1) * (position + 1) := by ring

theorem positionRangeTime_le (recipes : List Recipe)
    (firstPosition count : Nat) :
    positionRangeTime recipes firstPosition count ≤
      (3 * recipes.length + 2) * (count + 1) *
        (firstPosition + count + 1) := by
  induction count generalizing firstPosition with
  | zero =>
      simp [positionRangeTime]
      have positive :
          0 < (3 * recipes.length + 2) * (firstPosition + 1) :=
        Nat.mul_pos (by omega) (by omega)
      omega
  | succ count induction =>
      rw [positionRangeTime]
      have current := templateTime_le recipes firstPosition
      have rest := induction (firstPosition + 1)
      nlinarith

theorem selectedCount_le_length {Data : Type} (selected : Data → Bool)
    (workspace : List (Workspace Data)) :
    selectedCount selected workspace ≤ workspace.length := by
  exact UnaryPolynomialPaddingMachine.selectedCount_le_length
    (dataSelected selected) workspace

theorem appendedOutput_length {Data : Type} (selected : Data → Bool)
    (recipes : List Recipe) (ending : List UnaryProgramTokens.Token)
    (workspace : List (Workspace Data)) :
    (appendedOutput selected recipes ending workspace).length =
      workspace.length +
        (positionRangeTokens recipes 0
          (selectedCount selected workspace)).length + ending.length := by
  simp [appendedOutput, Nat.add_assoc]

theorem emittedRange_length_le_workspace {Data : Type}
    (selected : Data → Bool) (recipes : List Recipe)
    (workspace : List (Workspace Data)) :
    (positionRangeTokens recipes 0
        (selectedCount selected workspace)).length ≤
      templateWeight recipes * (workspace.length + 1) ^ 2 := by
  let count := selectedCount selected workspace
  have countLe : count ≤ workspace.length :=
    selectedCount_le_length selected workspace
  have rangeBound := positionRangeTokens_length_le recipes 0 count
  have firstLe : count ≤ workspace.length + 1 :=
    countLe.trans (Nat.le_succ _)
  have secondLe : count + 1 ≤ workspace.length + 1 :=
    Nat.add_le_add_right countLe 1
  have productLe : count * (count + 1) ≤
      (workspace.length + 1) * (workspace.length + 1) :=
    Nat.mul_le_mul firstLe secondLe
  have weightedLe := Nat.mul_le_mul_left (templateWeight recipes) productLe
  dsimp only [count] at rangeBound ⊢
  rw [pow_two]
  exact rangeBound.trans (by simpa [Nat.mul_assoc] using weightedLe)

theorem positionRangeTime_le_workspace {Data : Type}
    (selected : Data → Bool) (recipes : List Recipe)
    (workspace : List (Workspace Data)) :
    positionRangeTime recipes 0 (selectedCount selected workspace) ≤
      (3 * recipes.length + 2) * (workspace.length + 1) ^ 2 := by
  let count := selectedCount selected workspace
  have countLe : count ≤ workspace.length :=
    selectedCount_le_length selected workspace
  have rangeBound := positionRangeTime_le recipes 0 count
  have sideLe : count + 1 ≤ workspace.length + 1 :=
    Nat.add_le_add_right countLe 1
  have squareLe : (count + 1) * (count + 1) ≤
      (workspace.length + 1) * (workspace.length + 1) :=
    Nat.mul_le_mul sideLe sideLe
  have weightedLe := Nat.mul_le_mul_left (3 * recipes.length + 2) squareLe
  dsimp only [count] at rangeBound ⊢
  rw [pow_two]
  exact rangeBound.trans (by simpa [Nat.mul_assoc] using weightedLe)

/-- A fixed quadratic bound for one fixed affine template stage. -/
noncomputable def timePolynomial (recipes : List Recipe)
    (ending : List UnaryProgramTokens.Token) : Polynomial Nat :=
  Polynomial.C
      (templateWeight recipes + 3 * recipes.length + ending.length + 7) *
    (Polynomial.X + Polynomial.C 1) ^ 2

@[simp]
theorem timePolynomial_eval (recipes : List Recipe)
    (ending : List UnaryProgramTokens.Token) (length : Nat) :
    (timePolynomial recipes ending).eval length =
      (templateWeight recipes + 3 * recipes.length + ending.length + 7) *
        (length + 1) ^ 2 := by
  simp [timePolynomial, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_pow]

theorem totalTime_le_polynomial_eval {Data : Type}
    (selected : Data → Bool) (recipes : List Recipe)
    (ending : List UnaryProgramTokens.Token)
    (workspace : List (Workspace Data)) :
    totalTime selected recipes ending workspace ≤
      (timePolynomial recipes ending).eval workspace.length := by
  rw [timePolynomial_eval]
  have countBound := selectedCount_le_length selected workspace
  have rangeTimeBound :=
    positionRangeTime_le_workspace selected recipes workspace
  have emittedBound :=
    emittedRange_length_le_workspace selected recipes workspace
  unfold totalTime
  rw [appendedOutput_length]
  have squareOne : 1 ≤ (workspace.length + 1) ^ 2 := by
    nlinarith
  have endingBound : ending.length ≤
      ending.length * (workspace.length + 1) ^ 2 := by
    simpa using Nat.mul_le_mul_left ending.length squareOne
  have linearBound : 3 * workspace.length + 4 ≤
      5 * (workspace.length + 1) ^ 2 := by
    nlinarith
  have remainderBound : 3 * workspace.length + ending.length + 4 ≤
      (ending.length + 5) * (workspace.length + 1) ^ 2 := by
    calc
      3 * workspace.length + ending.length + 4 =
          (3 * workspace.length + 4) + ending.length := by omega
      _ ≤ 5 * (workspace.length + 1) ^ 2 +
          ending.length * (workspace.length + 1) ^ 2 :=
        Nat.add_le_add linearBound endingBound
      _ = (ending.length + 5) * (workspace.length + 1) ^ 2 := by
        ring
  calc
    workspace.length + 1 +
          positionRangeTime recipes 0 (selectedCount selected workspace) +
          1 + (selectedCount selected workspace + 1) +
          (workspace.length +
            (positionRangeTokens recipes 0
              (selectedCount selected workspace)).length + ending.length) +
          1 ≤
        (3 * recipes.length + 2) * (workspace.length + 1) ^ 2 +
          templateWeight recipes * (workspace.length + 1) ^ 2 +
          (3 * workspace.length + ending.length + 4) := by omega
    _ ≤ (3 * recipes.length + 2) * (workspace.length + 1) ^ 2 +
          templateWeight recipes * (workspace.length + 1) ^ 2 +
          ((ending.length + 5) * (workspace.length + 1) ^ 2) :=
      Nat.add_le_add_left remainderBound _
    _ = (templateWeight recipes + 3 * recipes.length + ending.length + 7) *
          (workspace.length + 1) ^ 2 := by ring

/-- For fixed recipes and ending, affine template emission is polynomial-time
in the complete retained workspace length. -/
noncomputable def computableInPolyTime {Data : Type} [Fintype Data]
    [Inhabited Data] (selected : Data → Bool) (recipes : List Recipe)
    (ending : List UnaryProgramTokens.Token) :
    @TM2ComputableInPolyTime
      (List (Workspace Data)) (List (Workspace Data))
      (Workspace Data) (Workspace Data) id id
      (appendedOutput selected recipes ending) where
  tm := machine Data selected recipes ending
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := timePolynomial recipes ending
  outputsFun workspace := by
    have run := machine_outputsInTime selected recipes ending workspace
    have run' : TM2OutputsInTime (machine Data selected recipes ending)
        (List.map (Equiv.refl (Workspace Data)).invFun (id workspace))
        (some (List.map (Equiv.refl (Workspace Data)).invFun
          (id (appendedOutput selected recipes ending workspace))))
        (totalTime selected recipes ending workspace) := by
      simpa only [FiniteBlockTransducer.map_refl_invFun, id_eq] using run
    exact
      { toEvalsTo := run'.toEvalsTo
        steps_le_m := run'.steps_le_m.trans
          (totalTime_le_polynomial_eval selected recipes ending workspace) }

end AffineTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
