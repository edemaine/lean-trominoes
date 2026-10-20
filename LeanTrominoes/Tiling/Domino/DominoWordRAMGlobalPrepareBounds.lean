/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMGlobalPrepare128

/-! # Polynomial time and logarithmic word bounds for global preparation -/
namespace LeanTrominoes.Domino.WordRAM.Binary.GlobalPrepare128
open ComplexityAbstract.RAM

noncomputable def resourceCoefficient (d : Nat) :=
  3*factor d+11*d*d+15*d+2*DeterminantSetup.slots d+69
noncomputable def timeCoefficient (d : Nat) :=
  4*factor d+18*(d*d+2*d)+68*(DeterminantSetup.compiled d).nodes.length+150

theorem inputEnd_le_size {n d : Nat} (B : BasisData n d) : inputEnd B≤WordRAM.size B := by
  unfold inputEnd WordRAM.size
  rw [WordRAM.words_eq_map,List.length_map]
  omega

theorem resource_polynomial {n d : Nat} (B : BasisData n d) :
    resourceBound B≤resourceCoefficient d*(WordRAM.size B+1) := by
  have nBound := (WordRAM.size_controls B).1
  have inputBound := inputEnd_le_size B
  have lengthBound := (WordRAM.size_controls B).2.2
  have exactBound : resourceBound B=n+6*inputEnd B+
      (2*factor d+6*d*d+9*d+DeterminantSetup.slots d+23)*WordRAM.precision B+
      (factor d+5*d*d+6*d+DeterminantSetup.slots d+39) := by
    unfold resourceBound BatchCopy.bound Circuit.resourceBound circuitBase endAddress
    ring
  rw [exactBound]
  calc
    _≤1*(WordRAM.size B+1)+6*(WordRAM.size B+1)+
        (2*factor d+6*d*d+9*d+DeterminantSetup.slots d+23)*(WordRAM.size B+1)+
        (factor d+5*d*d+6*d+DeterminantSetup.slots d+39)*(WordRAM.size B+1) := by
      have scaledLength := Nat.mul_le_mul_left (2*factor d+6*d*d+9*d+DeterminantSetup.slots d+23) (show WordRAM.precision B≤WordRAM.size B+1 by omega)
      have scaledInput := Nat.mul_le_mul_left 6 (show inputEnd B≤WordRAM.size B+1 by omega)
      have scaledConstant := Nat.mul_le_mul_left (factor d+5*d*d+6*d+DeterminantSetup.slots d+39) (show 1≤WordRAM.size B+1 by omega)
      simp only [Nat.mul_one] at scaledConstant
      omega
    _=resourceCoefficient d*(WordRAM.size B+1) := by unfold resourceCoefficient; ring

theorem resource_fits {n d w : Nat} (B : BasisData n d)
    (width : (Nat.log2 (resourceCoefficient d+1)+2)*Nat.log2 (WordRAM.size B+2)+2≤w) :
    Fits w (resourceBound B) := by
  apply LeanTrominoes.WordBounds.polynomial_fits_uniform (resourceCoefficient d) 1 (WordRAM.size B) w _ width
  simpa only [Int.natAbs_natCast,pow_one] using resource_polynomial B

theorem time_polynomial {n d : Nat} (B : BasisData n d) :
    8+costBound B≤timeCoefficient d*(WordRAM.size B+1)^2 := by
  have lengthBound := (WordRAM.size_controls B).2.2
  have squareBound : WordRAM.precision B^2≤(WordRAM.size B+1)^2 := Nat.pow_le_pow_left (by omega) 2
  have linearBound : WordRAM.precision B≤(WordRAM.size B+1)^2 := by nlinarith
  have unitBound : 1≤(WordRAM.size B+1)^2 := by nlinarith
  have factorBound := Nat.mul_le_mul_left (4*factor d) linearBound
  have arityBound := Nat.mul_le_mul_right (d*d+2*d) (show 7*WordRAM.precision B+11≤18*(WordRAM.size B+1)^2 by omega)
  have circuitBound := Nat.mul_le_mul_right (DeterminantSetup.compiled d).nodes.length
    (show 26*WordRAM.precision B^2+26*WordRAM.precision B+16≤68*(WordRAM.size B+1)^2 by omega)
  have finalLength := Nat.mul_le_mul_left 29 linearBound
  have finalConstant := Nat.mul_le_mul_left 121 unitBound
  simp only [Nat.mul_one] at finalConstant
  calc
    _=4*factor d*WordRAM.precision B+(7*WordRAM.precision B+11)*(d*d+2*d)+
        (26*WordRAM.precision B^2+26*WordRAM.precision B+16)*(DeterminantSetup.compiled d).nodes.length+
        29*WordRAM.precision B+121 := by unfold costBound determinantCost; ring
    _≤(4*factor d)*(WordRAM.size B+1)^2+(18*(WordRAM.size B+1)^2)*(d*d+2*d)+
        (68*(WordRAM.size B+1)^2)*(DeterminantSetup.compiled d).nodes.length+
        29*(WordRAM.size B+1)^2+121*(WordRAM.size B+1)^2 := by omega
    _=timeCoefficient d*(WordRAM.size B+1)^2 := by unfold timeCoefficient; ring

end LeanTrominoes.Domino.WordRAM.Binary.GlobalPrepare128
