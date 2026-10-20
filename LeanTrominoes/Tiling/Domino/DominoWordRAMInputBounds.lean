/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMInput

/-! # Common precision for all signed decoder circuit outputs -/
namespace LeanTrominoes.Domino.WordRAM
open ComplexityAbstract.RAM
variable {n d : ℕ}

theorem entryBits_le_core (B : BasisData n d) : entryBits B≤corePrecision B := by
  have coefficient : 1≤decoderWordFactor d+determinantWordFactor d := by
    unfold decoderWordFactor
    omega
  unfold corePrecision
  nlinarith

theorem input_basis_fits (B : BasisData n d) (i j : Fin d) : Fits (precision B) (B.basis i j) :=
  LeanTrominoes.WordBounds.fits_mono ((entryBits_le_core B).trans (by simp [precision])) (basis_fits B i j)

theorem input_origin_fits (B : BasisData n d) (v : Fin n) (i : Fin d) : Fits (precision B) (B.origin v i) :=
  LeanTrominoes.WordBounds.fits_mono ((entryBits_le_core B).trans (by simp [precision])) (origin_fits B v i)

/-- Each adjugate product in a neighboring-cell probe fits the declared
signed circuit precision. Integer magnitudes may greatly exceed one machine
word; these bounds choose the number of binary digits, not a larger RAM word. -/
theorem numerator_fits (B : BasisData n d) (u v : Fin n) (direction i : Fin d) :
    Fits (corePrecision B) (B.basis.adjugate.mulVec (B.origin u+unit direction-B.origin v) i) := by
  let bound : ℕ := 2^entryBits B
  have positive : 1≤bound := Nat.one_le_two_pow
  have origins := fun v i => LeanTrominoes.WordBounds.natAbs_le_of_fits (origin_fits B v i)
  have matrix := fun i j => LeanTrominoes.WordBounds.natAbs_le_of_fits (basis_fits B i j)
  obtain ⟨_,numerators,_,_⟩ := B.probe_magnitudes bound positive origins matrix (B.origin u+unit direction)
    (B.neighbor_magnitude bound origins u direction) v
  have dimension : 0< d := by have := i.isLt; omega
  have factor : 1≤d*bound := Nat.mul_pos dimension (by omega)
  have scaled := Nat.mul_le_mul_right (coordinateMagnitude d bound) factor
  have reconstruction : coordinateMagnitude d bound≤reconstructionMagnitude d bound := by
    unfold reconstructionMagnitude
    have step : coordinateMagnitude d bound≤d*bound*coordinateMagnitude d bound := by simpa using scaled
    omega
  have magnitude := (numerators i).trans (reconstruction.trans (reconstruction_polynomial bound d))
  have fits := LeanTrominoes.WordBounds.polynomial_fits_words (1+3*d*d*d.factorial) (d+2)
    (entryBits B) _ (entryBits_positive B) magnitude
  change Fits (decoderWordFactor d*entryBits B) _ at fits
  apply LeanTrominoes.WordBounds.fits_mono (fits := fits)
  unfold corePrecision
  nlinarith

/-- The per-probe difference vector uses the same precision as all other
circuit inputs, without changing the machine word width. -/
theorem difference_fits (B : BasisData n d) (u v : Fin n) (direction i : Fin d) :
    Fits (corePrecision B) ((B.origin u+unit direction-B.origin v) i) := by
  let bound : ℕ := 2^entryBits B
  have origins := fun v i => LeanTrominoes.WordBounds.natAbs_le_of_fits (origin_fits B v i)
  have matrix := fun i j => LeanTrominoes.WordBounds.natAbs_le_of_fits (basis_fits B i j)
  obtain ⟨difference,_,_,_⟩ := B.probe_magnitudes bound Nat.one_le_two_pow origins matrix
    (B.origin u+unit direction) (B.neighbor_magnitude bound origins u direction) v
  have magnitude : ((B.origin u+unit direction-B.origin v) i).natAbs≤3*(bound+1)^1 := by
    have := difference i
    simp only [pow_one]
    omega
  have fits := LeanTrominoes.WordBounds.polynomial_fits_words 3 1 (entryBits B) _ (entryBits_positive B) magnitude
  norm_num at fits
  have coefficient : 7≤decoderWordFactor d+determinantWordFactor d := by
    unfold decoderWordFactor
    omega
  apply LeanTrominoes.WordBounds.fits_mono (fits := fits)
  unfold corePrecision
  nlinarith

end LeanTrominoes.Domino.WordRAM
