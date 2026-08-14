/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIndexedTemplateEmitterBounds

/-!
# Polynomial runtime of indexed template emission

Package the exact whole-machine execution and fixed-family quantitative bounds
as a quadratic polynomial-time TM2 computation.
-/

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace IndexedTemplateEmitterMachine

open IndexedTemplateEmitter

/-- A fixed quadratic time bound for one fixed finite indexed family. -/
noncomputable def timePolynomial {Data : Type} [Fintype Data]
    (family : Family Data) : Polynomial Nat :=
  Polynomial.C
      (3 * familyRecipeCount family + familyWeight family + 6) *
    (Polynomial.X + Polynomial.C 1) ^ 2

@[simp]
theorem timePolynomial_eval {Data : Type} [Fintype Data]
    (family : Family Data) (length : Nat) :
    (timePolynomial family).eval length =
      (3 * familyRecipeCount family + familyWeight family + 6) *
        (length + 1) ^ 2 := by
  simp [timePolynomial, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_pow]

theorem totalTime_le_polynomial_eval {Data : Type} [Fintype Data]
    (family : Family Data) (data : List Data) :
    totalTime family data ≤
      (timePolynomial family).eval data.length := by
  rw [timePolynomial_eval]
  let scanCoefficient := 3 * familyRecipeCount family + 2
  have scanned := scanTime_le family 0 data
  have scanned' : scanTime family 0 data ≤
      scanCoefficient * data.length * (data.length + 1) + 1 := by
    simpa [scanCoefficient] using scanned
  have emitted := emitted_length_le family data
  have selected := selectedCount_le_length family data
  have productLe : data.length * (data.length + 1) ≤
      (data.length + 1) ^ 2 := by
    rw [pow_two]
    exact Nat.mul_le_mul_right (data.length + 1) (Nat.le_succ _)
  have scannedSquare : scanTime family 0 data ≤
      scanCoefficient * (data.length + 1) ^ 2 + 1 :=
    scanned'.trans (Nat.add_le_add_right
      (by
        simpa only [Nat.mul_assoc] using
          Nat.mul_le_mul_left scanCoefficient productLe) 1)
  have emittedSquare :
      (IndexedTemplateEmitter.emitted family data).length ≤
        familyWeight family * (data.length + 1) ^ 2 :=
    emitted.trans (by
      simpa only [Nat.mul_assoc] using
        Nat.mul_le_mul_left (familyWeight family) productLe)
  have remainder : 2 * data.length + 4 ≤
      4 * (data.length + 1) ^ 2 := by
    nlinarith [show 0 ≤ data.length ^ 2 from Nat.zero_le _]
  unfold totalTime
  calc
    scanTime family 0 data +
          (IndexedTemplateEmitter.selectedCount family data + 1) +
          (IndexedTemplateEmitter.emitted family data).length + 1 +
          data.length + 1 ≤
        scanCoefficient * (data.length + 1) ^ 2 +
          familyWeight family * (data.length + 1) ^ 2 +
          (2 * data.length + 4) := by omega
    _ ≤ scanCoefficient * (data.length + 1) ^ 2 +
          familyWeight family * (data.length + 1) ^ 2 +
          4 * (data.length + 1) ^ 2 :=
      Nat.add_le_add_left remainder _
    _ = (3 * familyRecipeCount family + familyWeight family + 6) *
          (data.length + 1) ^ 2 := by
      simp [scanCoefficient]
      ring

/-- For every fixed finite data-indexed recipe family, indexed template
emission is polynomial time in the complete retained input length. -/
noncomputable def computableInPolyTime {Data : Type} [Fintype Data]
    [Inhabited Data] (family : Family Data) :
    @TM2ComputableInPolyTime
      (List Data) (List (Data ⊕ UnaryProgramTokens.Token))
      Data (Data ⊕ UnaryProgramTokens.Token) id id
      (appendedOutput family) where
  tm := machine Data family
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := timePolynomial family
  outputsFun data := by
    have run := machine_outputsInTime family data
    have run' : TM2OutputsInTime (machine Data family)
        (List.map (Equiv.refl Data).invFun (id data))
        (some (List.map
          (Equiv.refl (Data ⊕ UnaryProgramTokens.Token)).invFun
          (id (appendedOutput family data))))
        (totalTime family data) := by
      simpa only [FiniteBlockTransducer.map_refl_invFun, id_eq] using run
    exact
      { toEvalsTo := run'.toEvalsTo
        steps_le_m := run'.steps_le_m.trans
          (totalTime_le_polynomial_eval family data) }

end IndexedTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
