/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTriangularTemplateEmitterBounds

/-!
# Polynomial time of the triangular emitter

The fixed-parameter local bounds are specialized to selector counts, each at
most the retained workspace length.  Both exact output length and exact
execution time are bounded by a fixed cubic polynomial, yielding the standard
`TM2ComputableInPolyTime` certificate.
-/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF
namespace TriangularTemplateEmitterMachine

open UnaryProgramTokens
open TriangularTemplateEmitter

theorem selectedCount_le_length {Data : Type} (selected : Data → Bool)
    (workspace : List (Workspace Data)) :
    selectedCount selected workspace ≤ workspace.length := by
  exact UnaryPolynomialPaddingMachine.selectedCount_le_length
    (dataSelected selected) workspace

theorem one_le_succ_cube (length : Nat) :
    1 ≤ (length + 1) ^ 3 := by
  exact one_le_pow₀ (by omega)

theorem succ_length_le_succ_cube (length : Nat) :
    length + 1 ≤ (length + 1) ^ 3 := by
  have squareOne : 1 ≤ (length + 1) ^ 2 :=
    one_le_pow₀ (by omega)
  calc
    length + 1 = (length + 1) * 1 := by simp
    _ ≤ (length + 1) * (length + 1) ^ 2 :=
      Nat.mul_le_mul_left (length + 1) squareOne
    _ = (length + 1) ^ 3 := by ring

theorem length_le_succ_cube (length : Nat) :
    length ≤ (length + 1) ^ 3 :=
  (Nat.le_succ length).trans (succ_length_le_succ_cube length)

theorem emitted_length {Data : Type} (parameters : Parameters Data)
    (first count : Nat) :
    (TriangularTemplateEmitter.emitted parameters.outerFirst parameters.inner
      parameters.outerSecond parameters.innerBase parameters.innerCloser
      parameters.frameCloser parameters.finalBase parameters.finalCloser first
      count).length =
        (frameRangeTokens parameters first 0 count).length +
          parameters.finalBase.length +
          parameters.finalCloser.length * count := by
  have semantic := frameRangeTokens_append_final parameters first 0 count
  have lengths := congrArg List.length semantic
  simpa [TriangularTemplateEmitter.emitted, List.length_append,
    repeatTokens_length, Nat.add_assoc] using lengths.symm

theorem appendedOutput_length {Data : Type} (parameters : Parameters Data)
    (workspace : List (Workspace Data)) :
    (appendedOutput parameters.firstSelected parameters.secondSelected
      parameters.outerFirst parameters.inner parameters.outerSecond
      parameters.innerBase parameters.innerCloser parameters.frameCloser
      parameters.finalBase parameters.finalCloser workspace).length =
        workspace.length +
          (TriangularTemplateEmitter.emitted parameters.outerFirst
            parameters.inner parameters.outerSecond parameters.innerBase
            parameters.innerCloser parameters.frameCloser parameters.finalBase
            parameters.finalCloser
            (selectedCount parameters.firstSelected workspace)
            (selectedCount parameters.secondSelected workspace)).length := by
  simp [appendedOutput]

theorem frameRangeTokens_length_le_workspace {Data : Type}
    (parameters : Parameters Data) (workspace : List (Workspace Data)) :
    (frameRangeTokens parameters
      (selectedCount parameters.firstSelected workspace) 0
      (selectedCount parameters.secondSelected workspace)).length ≤
        2 * frameWeight parameters * (workspace.length + 1) ^ 3 := by
  let first := selectedCount parameters.firstSelected workspace
  let count := selectedCount parameters.secondSelected workspace
  have firstLe : first ≤ workspace.length :=
    selectedCount_le_length parameters.firstSelected workspace
  have countLe : count ≤ workspace.length :=
    selectedCount_le_length parameters.secondSelected workspace
  have localBound := frameRangeTokens_length_le parameters first 0 count
  have countSide : count + 1 ≤ workspace.length + 1 := by omega
  have squareBound : (count + 1) * (count + 1) ≤
      (workspace.length + 1) * (workspace.length + 1) :=
    Nat.mul_le_mul countSide countSide
  have sumBound : first + count + 2 ≤ 2 * (workspace.length + 1) := by
    omega
  have productBound := Nat.mul_le_mul squareBound sumBound
  have productLe : (count + 1) ^ 2 * (first + count + 2) ≤
      2 * (workspace.length + 1) ^ 3 := by
    calc
      _ = ((count + 1) * (count + 1)) * (first + count + 2) := by
        ring
      _ ≤ ((workspace.length + 1) * (workspace.length + 1)) *
          (2 * (workspace.length + 1)) := productBound
      _ = _ := by ring
  have weighted := Nat.mul_le_mul_left (frameWeight parameters) productLe
  dsimp only [first, count] at localBound ⊢
  calc
    _ ≤ frameWeight parameters * ((count + 1) ^ 2 *
          (first + count + 2)) := by
      simpa [Nat.mul_assoc] using localBound
    _ ≤ frameWeight parameters * (2 * (workspace.length + 1) ^ 3) :=
      weighted
    _ = 2 * frameWeight parameters * (workspace.length + 1) ^ 3 := by
      ring

theorem outerFrameRangeTime_le_workspace {Data : Type}
    (parameters : Parameters Data) (workspace : List (Workspace Data)) :
    outerFrameRangeTime parameters
      (selectedCount parameters.firstSelected workspace) 0
      (selectedCount parameters.secondSelected workspace) ≤
        2 * frameTimeWeight parameters * (workspace.length + 1) ^ 3 := by
  let first := selectedCount parameters.firstSelected workspace
  let count := selectedCount parameters.secondSelected workspace
  have firstLe : first ≤ workspace.length :=
    selectedCount_le_length parameters.firstSelected workspace
  have countLe : count ≤ workspace.length :=
    selectedCount_le_length parameters.secondSelected workspace
  have localBound := outerFrameRangeTime_le parameters first 0 count
  have countSide : count + 1 ≤ workspace.length + 1 := by omega
  have squareBound : (count + 1) * (count + 1) ≤
      (workspace.length + 1) * (workspace.length + 1) :=
    Nat.mul_le_mul countSide countSide
  have sumBound : first + count + 2 ≤ 2 * (workspace.length + 1) := by
    omega
  have productBound := Nat.mul_le_mul squareBound sumBound
  have productLe : (count + 1) ^ 2 * (first + count + 2) ≤
      2 * (workspace.length + 1) ^ 3 := by
    calc
      _ = ((count + 1) * (count + 1)) * (first + count + 2) := by
        ring
      _ ≤ ((workspace.length + 1) * (workspace.length + 1)) *
          (2 * (workspace.length + 1)) := productBound
      _ = _ := by ring
  have weighted := Nat.mul_le_mul_left (frameTimeWeight parameters) productLe
  dsimp only [first, count] at localBound ⊢
  calc
    _ ≤ frameTimeWeight parameters * ((count + 1) ^ 2 *
          (first + count + 2)) := by
      simpa [Nat.mul_assoc] using localBound
    _ ≤ frameTimeWeight parameters * (2 * (workspace.length + 1) ^ 3) :=
      weighted
    _ = 2 * frameTimeWeight parameters * (workspace.length + 1) ^ 3 := by
      ring

theorem emitted_length_le_workspace {Data : Type}
    (parameters : Parameters Data) (workspace : List (Workspace Data)) :
    (TriangularTemplateEmitter.emitted parameters.outerFirst parameters.inner
      parameters.outerSecond parameters.innerBase parameters.innerCloser
      parameters.frameCloser parameters.finalBase parameters.finalCloser
      (selectedCount parameters.firstSelected workspace)
      (selectedCount parameters.secondSelected workspace)).length ≤
        (2 * frameWeight parameters + parameters.finalBase.length +
          parameters.finalCloser.length) * (workspace.length + 1) ^ 3 := by
  let count := selectedCount parameters.secondSelected workspace
  have countLe : count ≤ workspace.length :=
    selectedCount_le_length parameters.secondSelected workspace
  have frames := frameRangeTokens_length_le_workspace parameters workspace
  have cubeOne := one_le_succ_cube workspace.length
  have countCube : count ≤ (workspace.length + 1) ^ 3 :=
    countLe.trans (length_le_succ_cube workspace.length)
  have baseBound : parameters.finalBase.length ≤
      parameters.finalBase.length * (workspace.length + 1) ^ 3 := by
    simpa using Nat.mul_le_mul_left parameters.finalBase.length cubeOne
  have closerBound : parameters.finalCloser.length * count ≤
      parameters.finalCloser.length * (workspace.length + 1) ^ 3 :=
    Nat.mul_le_mul_left parameters.finalCloser.length countCube
  rw [emitted_length]
  dsimp only [count] at countLe closerBound ⊢
  calc
    _ ≤ 2 * frameWeight parameters * (workspace.length + 1) ^ 3 +
          parameters.finalBase.length * (workspace.length + 1) ^ 3 +
          parameters.finalCloser.length * (workspace.length + 1) ^ 3 := by
      omega
    _ = _ := by ring

theorem appendedOutput_length_le_workspace {Data : Type}
    (parameters : Parameters Data) (workspace : List (Workspace Data)) :
    (appendedOutput parameters.firstSelected parameters.secondSelected
      parameters.outerFirst parameters.inner parameters.outerSecond
      parameters.innerBase parameters.innerCloser parameters.frameCloser
      parameters.finalBase parameters.finalCloser workspace).length ≤
        (2 * frameWeight parameters + parameters.finalBase.length +
          parameters.finalCloser.length + 1) *
            (workspace.length + 1) ^ 3 := by
  rw [appendedOutput_length]
  have emittedBound := emitted_length_le_workspace parameters workspace
  have workspaceBound := length_le_succ_cube workspace.length
  calc
    _ ≤ (workspace.length + 1) ^ 3 +
        (2 * frameWeight parameters + parameters.finalBase.length +
          parameters.finalCloser.length) * (workspace.length + 1) ^ 3 :=
      Nat.add_le_add workspaceBound emittedBound
    _ = _ := by ring

/-- Fixed cubic bound for a fixed triangular emitter instance. -/
noncomputable def timePolynomial {Data : Type} (parameters : Parameters Data) :
    Polynomial Nat :=
  Polynomial.C
      (2 * frameTimeWeight parameters + 2 * frameWeight parameters +
        parameters.finalBase.length + parameters.finalCloser.length + 7) *
    (Polynomial.X + Polynomial.C 1) ^ 3

@[simp]
theorem timePolynomial_eval {Data : Type} (parameters : Parameters Data)
    (length : Nat) :
    (timePolynomial parameters).eval length =
      (2 * frameTimeWeight parameters + 2 * frameWeight parameters +
        parameters.finalBase.length + parameters.finalCloser.length + 7) *
          (length + 1) ^ 3 := by
  simp [timePolynomial, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_pow]

theorem totalTime_le_polynomial_eval {Data : Type}
    (parameters : Parameters Data) (workspace : List (Workspace Data)) :
    totalTime parameters workspace ≤
      (timePolynomial parameters).eval workspace.length := by
  rw [timePolynomial_eval]
  have firstLe := selectedCount_le_length parameters.firstSelected workspace
  have countLe := selectedCount_le_length parameters.secondSelected workspace
  have rangeTime := outerFrameRangeTime_le_workspace parameters workspace
  have outputBound := appendedOutput_length_le_workspace parameters workspace
  have cubeOne := one_le_succ_cube workspace.length
  have workspaceCube := length_le_succ_cube workspace.length
  have succWorkspaceCube := succ_length_le_succ_cube workspace.length
  have firstCube := firstLe.trans workspaceCube
  have countCube := countLe.trans workspaceCube
  have linearBound : workspace.length + 1 +
      (selectedCount parameters.secondSelected workspace + 2) +
      (selectedCount parameters.firstSelected workspace + 1) + 1 ≤
        6 * (workspace.length + 1) ^ 3 := by omega
  unfold totalTime
  calc
    workspace.length + 1 +
          outerFrameRangeTime parameters
            (selectedCount parameters.firstSelected workspace) 0
            (selectedCount parameters.secondSelected workspace) +
          (selectedCount parameters.secondSelected workspace + 2) +
          (selectedCount parameters.firstSelected workspace + 1) +
          (appendedOutput parameters.firstSelected parameters.secondSelected
            parameters.outerFirst parameters.inner parameters.outerSecond
            parameters.innerBase parameters.innerCloser parameters.frameCloser
            parameters.finalBase parameters.finalCloser workspace).length + 1 ≤
        2 * frameTimeWeight parameters * (workspace.length + 1) ^ 3 +
          (2 * frameWeight parameters + parameters.finalBase.length +
            parameters.finalCloser.length + 1) *
              (workspace.length + 1) ^ 3 +
          6 * (workspace.length + 1) ^ 3 := by omega
    _ = (2 * frameTimeWeight parameters + 2 * frameWeight parameters +
          parameters.finalBase.length + parameters.finalCloser.length + 7) *
            (workspace.length + 1) ^ 3 := by ring

/-- For fixed recipes and token blocks, triangular emission is polynomial-time
in the complete retained workspace length. -/
noncomputable def computableInPolyTime {Data : Type} [Fintype Data]
    [Inhabited Data] (parameters : Parameters Data) :
    @TM2ComputableInPolyTime
      (List (Workspace Data)) (List (Workspace Data))
      (Workspace Data) (Workspace Data) id id
      (appendedOutput parameters.firstSelected parameters.secondSelected
        parameters.outerFirst parameters.inner parameters.outerSecond
        parameters.innerBase parameters.innerCloser parameters.frameCloser
        parameters.finalBase parameters.finalCloser) where
  tm := machine Data parameters.firstSelected parameters.secondSelected
    parameters.outerFirst parameters.inner parameters.outerSecond
    parameters.innerBase parameters.innerCloser parameters.frameCloser
    parameters.finalBase parameters.finalCloser
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := timePolynomial parameters
  outputsFun workspace := by
    have run := machine_outputsInTime parameters workspace
    have run' : TM2OutputsInTime
        (machine Data parameters.firstSelected parameters.secondSelected
          parameters.outerFirst parameters.inner parameters.outerSecond
          parameters.innerBase parameters.innerCloser parameters.frameCloser
          parameters.finalBase parameters.finalCloser)
        (List.map (Equiv.refl (Workspace Data)).invFun (id workspace))
        (some (List.map (Equiv.refl (Workspace Data)).invFun
          (id (appendedOutput parameters.firstSelected
            parameters.secondSelected parameters.outerFirst parameters.inner
            parameters.outerSecond parameters.innerBase parameters.innerCloser
            parameters.frameCloser parameters.finalBase parameters.finalCloser
            workspace))))
        (totalTime parameters workspace) := by
      change TM2OutputsInTime
        (machine Data parameters.firstSelected parameters.secondSelected
          parameters.outerFirst parameters.inner parameters.outerSecond
          parameters.innerBase parameters.innerCloser parameters.frameCloser
          parameters.finalBase parameters.finalCloser)
        (List.map id workspace)
        (some (List.map id
          (appendedOutput parameters.firstSelected parameters.secondSelected
            parameters.outerFirst parameters.inner parameters.outerSecond
            parameters.innerBase parameters.innerCloser parameters.frameCloser
            parameters.finalBase parameters.finalCloser workspace)))
        (totalTime parameters workspace)
      simpa only [List.map_id_fun, id_eq] using run
    exact
      { toEvalsTo := run'.toEvalsTo
        steps_le_m := run'.steps_le_m.trans
          (totalTime_le_polynomial_eval parameters workspace) }

end TriangularTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
