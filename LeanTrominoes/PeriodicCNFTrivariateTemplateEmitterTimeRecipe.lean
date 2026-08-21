/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTrivariateTemplateEmitterExecution

/-! # Per-recipe bounds for the trivariate template emitter -/

namespace LeanTrominoes

namespace PeriodicCNF
namespace TrivariateTemplateEmitterMachine

open TrivariateTemplateEmitter

namespace Recipe

/-- Fixed coefficient bounding the unary output of one recipe. -/
def weight : Recipe → Nat
  | .fixed _ => 1
  | .atom base firstStride secondStride positionStride =>
      base + firstStride + secondStride + positionStride

theorem tokens_length_le (recipe : Recipe)
    (first second position : Nat) :
    (recipe.tokens first second position).length ≤
      recipe.weight * (first + second + position + 1) := by
  cases recipe with
  | fixed token =>
      simp [TrivariateTemplateEmitter.Recipe.tokens, weight]
  | atom base firstStride secondStride positionStride =>
      simp only [TrivariateTemplateEmitter.Recipe.tokens,
        List.length_replicate, weight]
      nlinarith

theorem time_le (recipe : Recipe) (first second position : Nat) :
    recipeTime first second position recipe ≤
      7 * (first + second + position + 1) := by
  cases recipe <;> simp [recipeTime] <;> omega

end Recipe

end TrivariateTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
