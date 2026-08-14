/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTriangularTemplateEmitterSemantics
import LeanTrominoes.PeriodicCNFBivariateTemplateEmitterTime

/-!
# Local quantitative bounds for the triangular emitter

This file bounds the output and runtime of templates, inner ranges, individual
frames, and complete frame ranges.  The coefficients depend only on the fixed
recipe/token parameters; the following module converts these bounds into one
cubic workspace-length polynomial.
-/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF
namespace TriangularTemplateEmitterMachine

open UnaryProgramTokens
open TriangularTemplateEmitter

theorem repeatTokens_length (tokens : List Token) (count : Nat) :
    (repeatTokens tokens count).length = tokens.length * count := by
  induction count with
  | zero => simp [repeatTokens]
  | succ count induction =>
      rw [repeatTokens, List.length_append, induction]
      ring

theorem outerRecipeTime_le (recipe : Recipe) (first position : Nat) :
    outerRecipeTime first position recipe ≤
      5 * (first + position + 1) := by
  cases recipe <;> simp [outerRecipeTime] <;> omega

theorem outerTemplateListTime_le (recipes : List Recipe)
    (first position : Nat) :
    (recipes.map (outerRecipeTime first position)).sum ≤
      5 * recipes.length * (first + position + 1) := by
  induction recipes with
  | nil => simp
  | cons recipe recipes induction =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have current := outerRecipeTime_le recipe first position
      nlinarith

theorem outerTemplateTime_le {Data : Type} (parameters : Parameters Data)
    (stage : Stage) (first position : Nat) :
    outerTemplateTime parameters stage first position ≤
      5 * (stageRecipes parameters.outerFirst parameters.inner
        parameters.outerSecond stage).length * (first + position + 1) := by
  exact outerTemplateListTime_le _ _ _

theorem innerRecipeTime_le (recipe : Recipe)
    (first outer innerCount : Nat) :
    innerRecipeTime first outer innerCount recipe ≤
      7 * (first + outer + innerCount + 1) := by
  cases recipe <;> simp [innerRecipeTime] <;> omega

theorem innerTemplateListTime_le (recipes : List Recipe)
    (first outer innerCount : Nat) :
    (recipes.map (innerRecipeTime first outer innerCount)).sum ≤
      7 * recipes.length * (first + outer + innerCount + 1) := by
  induction recipes with
  | nil => simp
  | cons recipe recipes induction =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have current := innerRecipeTime_le recipe first outer innerCount
      nlinarith

theorem innerTemplateTime_le {Data : Type} (parameters : Parameters Data)
    (first outer innerCount : Nat) :
    innerTemplateTime parameters first outer innerCount ≤
      7 * parameters.inner.length *
        (first + outer + innerCount + 1) := by
  exact innerTemplateListTime_le _ _ _ _

theorem innerPositionRangeTime_le {Data : Type}
    (parameters : Parameters Data) (first outer innerCount count : Nat) :
    innerPositionRangeTime parameters first outer innerCount count ≤
      (7 * parameters.inner.length + 2) * count *
        (first + outer + innerCount + count + 2) := by
  induction count generalizing innerCount with
  | zero => simp [innerPositionRangeTime]
  | succ count induction =>
      rw [innerPositionRangeTime]
      have current := innerTemplateTime_le parameters first outer innerCount
      have rest := induction (innerCount + 1)
      nlinarith

/-- Fixed coefficient bounding the token length of one frame. -/
def frameWeight {Data : Type} (parameters : Parameters Data) : Nat :=
  BivariateTemplateEmitterMachine.templateWeight parameters.outerFirst +
    BivariateTemplateEmitterMachine.templateWeight parameters.inner +
    BivariateTemplateEmitterMachine.templateWeight parameters.outerSecond +
    parameters.innerBase.length + parameters.innerCloser.length +
    parameters.frameCloser.length

theorem frameTokens_length_le {Data : Type} (parameters : Parameters Data)
    (first position higherCount : Nat) :
    (frameTokens parameters.outerFirst parameters.inner
      parameters.outerSecond parameters.innerBase parameters.innerCloser
      parameters.frameCloser first position higherCount).length ≤
        frameWeight parameters * (higherCount + 1) *
          (first + position + higherCount + 2) := by
  have outerFirstBound :=
    BivariateTemplateEmitterMachine.positionTokens_length_le
      parameters.outerFirst first position
  have innerBound :=
    BivariateTemplateEmitterMachine.positionRangeTokens_length_le
      parameters.inner first (position + 1) higherCount
  have outerSecondBound :=
    BivariateTemplateEmitterMachine.positionTokens_length_le
      parameters.outerSecond first position
  have repeated := repeatTokens_length parameters.innerCloser higherCount
  have sideBound : first + position + 1 ≤
      (higherCount + 1) * (first + position + higherCount + 2) := by
    nlinarith
  have unitBound : 1 ≤
      (higherCount + 1) * (first + position + higherCount + 2) := by
    nlinarith
  have countBound : higherCount ≤
      (higherCount + 1) * (first + position + higherCount + 2) := by
    nlinarith
  have outerFirstLift :
      (BivariateProgramTemplates.positionTokens parameters.outerFirst first
          position).length ≤
        BivariateTemplateEmitterMachine.templateWeight parameters.outerFirst *
          (higherCount + 1) * (first + position + higherCount + 2) :=
    outerFirstBound.trans (by
      simpa [Nat.mul_assoc] using Nat.mul_le_mul_left
        (BivariateTemplateEmitterMachine.templateWeight
          parameters.outerFirst) sideBound)
  have innerRaw :
      (BivariateTemplateEmitterMachine.positionRangeTokens parameters.inner
          first (position + 1) higherCount).length ≤
        BivariateTemplateEmitterMachine.templateWeight parameters.inner *
          higherCount * (first + position + higherCount + 2) := by
    convert innerBound using 1
    all_goals ring
  have innerLift :
      (BivariateTemplateEmitterMachine.positionRangeTokens parameters.inner
          first (position + 1) higherCount).length ≤
        BivariateTemplateEmitterMachine.templateWeight parameters.inner *
          (higherCount + 1) * (first + position + higherCount + 2) :=
    innerRaw.trans (by
      have countProduct := Nat.mul_le_mul_left
        (BivariateTemplateEmitterMachine.templateWeight parameters.inner)
        (Nat.le_succ higherCount)
      exact Nat.mul_le_mul_right (first + position + higherCount + 2)
        countProduct)
  have baseLift : parameters.innerBase.length ≤
      parameters.innerBase.length * (higherCount + 1) *
        (first + position + higherCount + 2) := by
    simpa [Nat.mul_assoc] using
      Nat.mul_le_mul_left parameters.innerBase.length unitBound
  have closerLift : (repeatTokens parameters.innerCloser higherCount).length ≤
      parameters.innerCloser.length * (higherCount + 1) *
        (first + position + higherCount + 2) := by
    rw [repeated]
    simpa [Nat.mul_assoc] using
      Nat.mul_le_mul_left parameters.innerCloser.length countBound
  have frameCloserLift : parameters.frameCloser.length ≤
      parameters.frameCloser.length * (higherCount + 1) *
        (first + position + higherCount + 2) := by
    simpa [Nat.mul_assoc] using
      Nat.mul_le_mul_left parameters.frameCloser.length unitBound
  have outerSecondLift :
      (BivariateProgramTemplates.positionTokens parameters.outerSecond first
          position).length ≤
        BivariateTemplateEmitterMachine.templateWeight parameters.outerSecond *
          (higherCount + 1) * (first + position + higherCount + 2) :=
    outerSecondBound.trans (by
      simpa [Nat.mul_assoc] using Nat.mul_le_mul_left
        (BivariateTemplateEmitterMachine.templateWeight
          parameters.outerSecond) sideBound)
  simp only [frameTokens, List.length_append]
  calc
    _ ≤ BivariateTemplateEmitterMachine.templateWeight
            parameters.outerFirst * (higherCount + 1) *
            (first + position + higherCount + 2) +
          BivariateTemplateEmitterMachine.templateWeight parameters.inner *
            (higherCount + 1) * (first + position + higherCount + 2) +
          parameters.innerBase.length * (higherCount + 1) *
            (first + position + higherCount + 2) +
          parameters.innerCloser.length * (higherCount + 1) *
            (first + position + higherCount + 2) +
          parameters.frameCloser.length * (higherCount + 1) *
            (first + position + higherCount + 2) +
          BivariateTemplateEmitterMachine.templateWeight
            parameters.outerSecond * (higherCount + 1) *
            (first + position + higherCount + 2) := by omega
    _ = frameWeight parameters * (higherCount + 1) *
          (first + position + higherCount + 2) := by
      unfold frameWeight
      ring

theorem frameRangeTokens_length_le {Data : Type}
    (parameters : Parameters Data) (first position count : Nat) :
    (frameRangeTokens parameters first position count).length ≤
      frameWeight parameters * (count + 1) ^ 2 *
        (first + position + count + 2) := by
  induction count generalizing position with
  | zero => simp [frameRangeTokens]
  | succ count induction =>
      rw [frameRangeTokens, List.length_append]
      have current := frameTokens_length_le parameters first position count
      have rest := induction (position + 1)
      nlinarith

/-- Fixed coefficient bounding the runtime of one frame. -/
def frameTimeWeight {Data : Type} (parameters : Parameters Data) : Nat :=
  5 * parameters.outerFirst.length +
    (7 * parameters.inner.length + 2) +
    5 * parameters.outerSecond.length + 4

theorem outerFrameTime_le {Data : Type} (parameters : Parameters Data)
    (first position higherCount : Nat) :
    outerFrameTime parameters first position higherCount ≤
      frameTimeWeight parameters * (higherCount + 1) *
        (first + position + higherCount + 2) := by
  have outerFirstBound := outerTemplateTime_le parameters .outerFirst
    first position
  have innerBound := innerPositionRangeTime_le parameters first position 0
    higherCount
  have outerSecondBound := outerTemplateTime_le parameters .outerSecond
    first position
  simp only [stageRecipes] at outerFirstBound outerSecondBound
  have sideBound : first + position + 1 ≤
      (higherCount + 1) * (first + position + higherCount + 2) := by
    nlinarith
  have outerFirstLift : outerTemplateTime parameters .outerFirst first
      position ≤
        5 * parameters.outerFirst.length * (higherCount + 1) *
          (first + position + higherCount + 2) :=
    outerFirstBound.trans (by
      simpa [Nat.mul_assoc] using Nat.mul_le_mul_left
        (5 * parameters.outerFirst.length) sideBound)
  have innerRaw : innerPositionRangeTime parameters first position 0
      higherCount ≤
        (7 * parameters.inner.length + 2) * higherCount *
          (first + position + higherCount + 2) := by
    convert innerBound using 1
    all_goals ring
  have innerLift : innerPositionRangeTime parameters first position 0
      higherCount ≤
        (7 * parameters.inner.length + 2) * (higherCount + 1) *
          (first + position + higherCount + 2) :=
    innerRaw.trans (by
      have countProduct := Nat.mul_le_mul_left
        (7 * parameters.inner.length + 2) (Nat.le_succ higherCount)
      exact Nat.mul_le_mul_right (first + position + higherCount + 2)
        countProduct)
  have outerSecondLift : outerTemplateTime parameters .outerSecond first
      position ≤
        5 * parameters.outerSecond.length * (higherCount + 1) *
          (first + position + higherCount + 2) :=
    outerSecondBound.trans (by
      simpa [Nat.mul_assoc] using Nat.mul_le_mul_left
        (5 * parameters.outerSecond.length) sideBound)
  have controlLift : higherCount + 2 + 2 ≤
      4 * (higherCount + 1) *
        (first + position + higherCount + 2) := by nlinarith
  unfold outerFrameTime
  calc
    _ ≤ 5 * parameters.outerFirst.length * (higherCount + 1) *
            (first + position + higherCount + 2) +
          (7 * parameters.inner.length + 2) * (higherCount + 1) *
            (first + position + higherCount + 2) +
          5 * parameters.outerSecond.length * (higherCount + 1) *
            (first + position + higherCount + 2) +
          4 * (higherCount + 1) *
            (first + position + higherCount + 2) := by omega
    _ = frameTimeWeight parameters * (higherCount + 1) *
          (first + position + higherCount + 2) := by
      unfold frameTimeWeight
      ring

theorem outerFrameRangeTime_le {Data : Type}
    (parameters : Parameters Data) (first position count : Nat) :
    outerFrameRangeTime parameters first position count ≤
      frameTimeWeight parameters * (count + 1) ^ 2 *
        (first + position + count + 2) := by
  induction count generalizing position with
  | zero => simp [outerFrameRangeTime]
  | succ count induction =>
      rw [outerFrameRangeTime]
      have current := outerFrameTime_le parameters first position count
      have rest := induction (position + 1)
      nlinarith

end TriangularTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
