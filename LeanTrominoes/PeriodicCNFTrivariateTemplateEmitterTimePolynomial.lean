/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTrivariateTemplateEmitterTimeWorkspace

/-! # A quadratic clock for the trivariate template emitter -/

namespace LeanTrominoes

open Computability

namespace PeriodicCNF
namespace TrivariateTemplateEmitterMachine

open UnaryProgramTokens

/-- A fixed quadratic clock for one fixed trivariate affine template stage. -/
noncomputable def timePolynomial (recipes : List Recipe)
    (ending : List Token) : Polynomial Nat :=
  Polynomial.C
      (3 * templateWeight recipes + 21 * recipes.length +
        ending.length + 12) *
    (Polynomial.X + Polynomial.C 1) ^ 2

@[simp]
theorem timePolynomial_eval (recipes : List Recipe)
    (ending : List Token) (length : Nat) :
    (timePolynomial recipes ending).eval length =
      (3 * templateWeight recipes + 21 * recipes.length +
        ending.length + 12) * (length + 1) ^ 2 := by
  simp [timePolynomial, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_pow]

theorem totalTime_le_polynomial_eval {Data : Type}
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (workspace : List (Workspace Data)) :
    totalTime firstSelected secondSelected positionSelected recipes ending
        workspace ≤
      (timePolynomial recipes ending).eval workspace.length := by
  rw [timePolynomial_eval]
  have firstCountBound : firstCountOf firstSelected workspace ≤
      workspace.length := by
    simpa [firstCountOf] using
      selectedCount_le_length firstSelected workspace
  have secondCountBound : secondCountOf secondSelected workspace ≤
      workspace.length := by
    simpa [secondCountOf] using
      selectedCount_le_length secondSelected workspace
  have positionCountBound : positionCountOf positionSelected workspace ≤
      workspace.length := by
    simpa [positionCountOf] using
      selectedCount_le_length positionSelected workspace
  have rangeTimeBound := positionRangeTime_le_workspace firstSelected
    secondSelected positionSelected recipes workspace
  have emittedBound := emittedRange_length_le_workspace firstSelected
    secondSelected positionSelected recipes workspace
  unfold totalTime prefixTime cleanupTime
  rw [emittedOutput_length]
  have squareOne : 1 ≤ (workspace.length + 1) ^ 2 := by
    nlinarith
  have endingBound : ending.length ≤
      ending.length * (workspace.length + 1) ^ 2 := by
    simpa using Nat.mul_le_mul_left ending.length squareOne
  have linearBound : 5 * workspace.length + 6 ≤
      6 * (workspace.length + 1) ^ 2 := by
    nlinarith
  have remainderBound : 5 * workspace.length + ending.length + 6 ≤
      (ending.length + 6) * (workspace.length + 1) ^ 2 := by
    calc
      5 * workspace.length + ending.length + 6 =
          (5 * workspace.length + 6) + ending.length := by omega
      _ ≤ 6 * (workspace.length + 1) ^ 2 +
          ending.length * (workspace.length + 1) ^ 2 :=
        Nat.add_le_add linearBound endingBound
      _ = (ending.length + 6) * (workspace.length + 1) ^ 2 := by
        ring
  calc
    (workspace.length + 1 +
          positionRangeTime recipes
            (firstCountOf firstSelected workspace)
            (secondCountOf secondSelected workspace) 0
            (positionCountOf positionSelected workspace) +
          1) +
          ((firstCountOf firstSelected workspace + 1) +
            (secondCountOf secondSelected workspace + 1) +
            (positionCountOf positionSelected workspace + 1)) +
          (workspace.length +
            (emittedOf firstSelected secondSelected positionSelected recipes
              workspace).length + ending.length) +
          1 ≤
        (3 * (7 * recipes.length + 2)) *
            (workspace.length + 1) ^ 2 +
          (3 * templateWeight recipes) * (workspace.length + 1) ^ 2 +
          (5 * workspace.length + ending.length + 6) := by
      omega
    _ ≤ (3 * (7 * recipes.length + 2)) *
            (workspace.length + 1) ^ 2 +
          (3 * templateWeight recipes) * (workspace.length + 1) ^ 2 +
          ((ending.length + 6) * (workspace.length + 1) ^ 2) :=
      Nat.add_le_add_left remainderBound _
    _ = (3 * templateWeight recipes + 21 * recipes.length +
          ending.length + 12) * (workspace.length + 1) ^ 2 := by
      ring

end TrivariateTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
