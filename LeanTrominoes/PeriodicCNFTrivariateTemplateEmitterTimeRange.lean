/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTrivariateTemplateEmitterTimeRecipe

/-! # Recipe-list and position-range bounds for the trivariate emitter -/

namespace LeanTrominoes

namespace PeriodicCNF
namespace TrivariateTemplateEmitterMachine

open TrivariateTemplateEmitter

/-- Sum of all fixed output coefficients in one position template. -/
def templateWeight (recipes : List Recipe) : Nat :=
  (recipes.map Recipe.weight).sum

theorem positionTokens_length_le (recipes : List Recipe)
    (first second position : Nat) :
    (positionTokens recipes first second position).length ≤
      templateWeight recipes * (first + second + position + 1) := by
  induction recipes with
  | nil =>
      simp [positionTokens, templateWeight]
  | cons recipe recipes induction =>
      simp only [positionTokens, List.flatMap_cons, List.length_append,
        templateWeight, List.map_cons, List.sum_cons]
      have current := Recipe.tokens_length_le recipe first second position
      calc
        (Recipe.tokens first second position recipe).length +
              (List.flatMap (Recipe.tokens first second position)
                recipes).length ≤
            recipe.weight * (first + second + position + 1) +
              templateWeight recipes * (first + second + position + 1) :=
          Nat.add_le_add current induction
        _ = (recipe.weight + templateWeight recipes) *
              (first + second + position + 1) := by ring

theorem positionRangeTokens_length_le (recipes : List Recipe)
    (first second firstPosition count : Nat) :
    (positionRangeTokens recipes first second firstPosition count).length ≤
      templateWeight recipes * count *
        (first + second + firstPosition + count + 1) := by
  induction count generalizing firstPosition with
  | zero => simp
  | succ count induction =>
      rw [positionRangeTokens_succ, List.length_append]
      have current :=
        positionTokens_length_le recipes first second firstPosition
      have rest := induction (firstPosition + 1)
      nlinarith

theorem templateTime_le (recipes : List Recipe)
    (first second position : Nat) :
    templateTime recipes first second position ≤
      7 * recipes.length * (first + second + position + 1) := by
  induction recipes with
  | nil => simp [templateTime]
  | cons recipe recipes induction =>
      simp only [templateTime, List.map_cons, List.sum_cons,
        List.length_cons]
      have current := Recipe.time_le recipe first second position
      calc
        recipeTime first second position recipe +
              (List.map (recipeTime first second position) recipes).sum ≤
            7 * (first + second + position + 1) +
              7 * recipes.length * (first + second + position + 1) :=
          Nat.add_le_add current induction
        _ = 7 * (recipes.length + 1) *
              (first + second + position + 1) := by ring

theorem positionRangeTime_le (recipes : List Recipe)
    (first second firstPosition count : Nat) :
    positionRangeTime recipes first second firstPosition count ≤
      (7 * recipes.length + 2) * (count + 1) *
        (first + second + firstPosition + count + 1) := by
  induction count generalizing firstPosition with
  | zero =>
      simp [positionRangeTime]
      have positive :
          0 < (7 * recipes.length + 2) *
            (first + second + firstPosition + 1) :=
        Nat.mul_pos (by omega) (by omega)
      omega
  | succ count induction =>
      rw [positionRangeTime]
      have current :=
        templateTime_le recipes first second firstPosition
      have rest := induction (firstPosition + 1)
      nlinarith

end TrivariateTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
