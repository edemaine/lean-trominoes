/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFlatEncodingSize
import LeanTrominoes.PeriodicCNFStripSourceFormula
import LeanTrominoes.PeriodicThreeCNFSize
import LeanTrominoes.PeriodicThreeSATThreeSize

/-!
# Size of the guarded CNF used by the strip reduction
-/

noncomputable section

namespace LeanTrominoes

open Computability

namespace PeriodicCNFFlatEncoding

private theorem fields_length_le_encoded_sum (fields : List Nat) :
  fields.length ≤
      (fields.map fun field =>
        (Computability.encodeNat field).length + 1).sum := by
  induction fields with
  | nil => simp
  | cons field fields induction =>
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      omega

theorem literalCount_eq_presentationLiteralCount
    (formula : PeriodicCNF Nat) :
    literalCount formula = PeriodicCNF.presentationLiteralCount formula := by
  rcases formula with ⟨clauses⟩
  simp [literalCount, PeriodicCNF.presentationLiteralCount]

/-- The flat encoding has at least one symbol per finite clause or literal
entry (in fact, it has considerably more). -/
theorem presentationSize_le_finEncoding_encode_length
    (formula : PeriodicCNF Nat) :
    PeriodicCNF.presentationSize formula ≤
      (finEncoding.encode formula).length := by
  have fields := fields_length_le_encoded_sum (formulaFields formula)
  rw [← finEncoding_encode_length] at fields
  calc
    PeriodicCNF.presentationSize formula ≤
        (formulaFields formula).length := by
      rw [formulaFields_length,
        literalCount_eq_presentationLiteralCount]
      unfold PeriodicCNF.presentationSize
      omega
    _ ≤ (finEncoding.encode formula).length := fields

end PeriodicCNFFlatEncoding

namespace PeriodicCNFStripReduction

/-- A convenient explicit quadratic budget for the guarded width-three,
three-occurrence source sent into the geometric reduction. -/
def sourceFormulaPresentationBudget (sourceSize : Nat) : Nat :=
  4 + 16 * sourceSize + 64 * sourceSize ^ 2

theorem normalizedFormula_presentationSize_le (source : PeriodicCNF Nat) :
    PeriodicCNF.presentationSize (normalizedFormula source) ≤
      16 * PeriodicCNF.presentationSize source +
        64 * PeriodicCNF.presentationSize source ^ 2 := by
  let three := PeriodicThreeCNF.formula source
  have threeSize : PeriodicCNF.presentationSize three ≤
      4 * PeriodicCNF.presentationSize source :=
    PeriodicThreeCNF.formula_presentationSize_le source
  have split := PeriodicThreeSATThree.formula_presentationSize_le three
    (PeriodicThreeCNF.formula_widthAtMostThree source)
  have square : PeriodicCNF.presentationSize three ^ 2 ≤
      (4 * PeriodicCNF.presentationSize source) ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul threeSize threeSize
  change PeriodicCNF.presentationSize
      (PeriodicThreeSATThree.formula three) ≤ _
  calc
    PeriodicCNF.presentationSize (PeriodicThreeSATThree.formula three) ≤
        4 * (PeriodicCNF.presentationSize three +
          PeriodicCNF.presentationSize three ^ 2) := split
    _ ≤ 4 * (4 * PeriodicCNF.presentationSize source +
          (4 * PeriodicCNF.presentationSize source) ^ 2) := by
      exact Nat.mul_le_mul_left 4 (Nat.add_le_add threeSize square)
    _ = 16 * PeriodicCNF.presentationSize source +
        64 * PeriodicCNF.presentationSize source ^ 2 := by ring

theorem fallbackFormula_presentationSize :
    PeriodicCNF.presentationSize fallbackFormula = 4 := by
  native_decide

/-- The total guarded normalization is quadratically bounded for both the
admissible and fixed-fallback branches. -/
theorem sourceFormula_presentationSize_le (source : PeriodicCNF Nat) :
    PeriodicCNF.presentationSize (sourceFormula source) ≤
      sourceFormulaPresentationBudget
        (PeriodicCNF.presentationSize source) := by
  by_cases admissible : SourceAdmissible source
  · rw [sourceFormula, if_pos admissible]
    have normalized := normalizedFormula_presentationSize_le source
    unfold sourceFormulaPresentationBudget
    omega
  · rw [sourceFormula, if_neg admissible,
      fallbackFormula_presentationSize]
    unfold sourceFormulaPresentationBudget
    omega

/-- The guarded presentation budget can be evaluated directly at the source
flat-encoding length. -/
theorem sourceFormula_presentationSize_le_flatLength
    (source : PeriodicCNF Nat) :
    PeriodicCNF.presentationSize (sourceFormula source) ≤
      sourceFormulaPresentationBudget
        (PeriodicCNFFlatEncoding.finEncoding.encode source).length := by
  have sizeLe :=
    PeriodicCNFFlatEncoding.presentationSize_le_finEncoding_encode_length source
  have squareLe : PeriodicCNF.presentationSize source ^ 2 ≤
      (PeriodicCNFFlatEncoding.finEncoding.encode source).length ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul sizeLe sizeLe
  exact (sourceFormula_presentationSize_le source).trans (by
    unfold sourceFormulaPresentationBudget
    omega)

end PeriodicCNFStripReduction
end LeanTrominoes
