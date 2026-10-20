/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.PeriodicDominoBasis
import Mathlib.Data.Int.NatAbs
import LeanTrominoes.Computation.RAM.WordBounds

/-! # Magnitude bounds for integer period decoding

For fixed dimension, determinant and coordinate arithmetic has polynomial
magnitude in the input entries. This does not bound those entries in the
number of representatives: `BasisData` permits arbitrary integers.
-/
namespace LeanTrominoes.Domino
variable {d : ℕ}

/-- Any partial sum of bounded integer terms has the corresponding magnitude bound. -/
theorem sum_magnitude {ι : Type*} (s : Finset ι) (f : ι → ℤ) (bound : ℕ)
    (h : ∀ i ∈ s, (f i).natAbs ≤ bound) :
    (∑ i ∈ s, f i).natAbs ≤ s.card*bound := by
  exact (Int.natAbs_sum_le s f).trans (by simpa using Finset.sum_le_sum h)

/-- The bound applies to every partial determinant product, not just its final value. -/
theorem product_magnitude {ι : Type*} (s : Finset ι) (f : ι → ℤ) (bound : ℕ)
    (h : ∀ i ∈ s, (f i).natAbs ≤ bound) :
    (∏ i ∈ s, f i).natAbs ≤ bound^s.card := by
  change Int.natAbsHom (∏ i ∈ s, f i) ≤ _
  rw [map_prod]
  exact (Finset.prod_le_prod h).trans_eq (by simp)

/-- Leibniz determinant magnitude, including cancellation-free accumulation. -/
theorem determinant_magnitude (A : Matrix (Fin d) (Fin d) ℤ) (bound : ℕ)
    (h : ∀ i j, (A i j).natAbs ≤ bound) :
    A.det.natAbs ≤ d.factorial*bound^d := by
  rw [Matrix.det_apply']
  have terms : ∀ σ : Equiv.Perm (Fin d),
      ((↑(Equiv.Perm.sign σ) : ℤ)*∏ i, A (σ i) i).natAbs ≤ bound^d := by
    intro σ
    rw [Int.natAbs_mul]
    have sign : (↑(Equiv.Perm.sign σ) : ℤ).natAbs=1 := by
      have unit := (Equiv.Perm.sign σ).isUnit
      rcases Int.isUnit_iff.mp unit with equal | equal <;> simp [equal]
    rw [sign,one_mul]
    simpa using product_magnitude Finset.univ (fun i => A (σ i) i) bound (fun i _ => h _ _)
  have bound := sum_magnitude Finset.univ _ (bound^d) (fun σ _ => terms σ)
  simpa [Fintype.card_perm] using bound

/-- Cramer's row replacement uses only original entries, zero, and one. -/
theorem adjugate_magnitude (A : Matrix (Fin d) (Fin d) ℤ) (bound : ℕ) (positive : 1≤bound)
    (h : ∀ i j, (A i j).natAbs ≤ bound) (i j : Fin d) :
    (A.adjugate i j).natAbs ≤ d.factorial*bound^d := by
  rw [Matrix.adjugate_apply]
  apply determinant_magnitude
  intro a b
  by_cases row : a=j
  · subst a
    simp only [Matrix.updateRow_self,Pi.single_apply]
    split <;> simp_all
  · simpa [Matrix.updateRow_apply, row] using h a b

/-- Every matrix-vector dot product is bounded by dimension times entry magnitudes. -/
theorem mulVec_magnitude (A : Matrix (Fin d) (Fin d) ℤ) (x : Fin d → ℤ)
    (matrixBound vectorBound : ℕ) (ha : ∀ i j, (A i j).natAbs ≤ matrixBound)
    (hx : ∀ i, (x i).natAbs ≤ vectorBound) (i : Fin d) :
    ((A.mulVec x) i).natAbs ≤ d*matrixBound*vectorBound := by
  change (∑ j, A i j*x j).natAbs ≤ _
  have bound := sum_magnitude Finset.univ (fun j => A i j*x j) (matrixBound*vectorBound)
    (fun j _ => by rw [Int.natAbs_mul]; exact Nat.mul_le_mul (ha i j) (hx j))
  simpa [Nat.mul_assoc] using bound

/-- Division by the determinant cannot increase the numerator's magnitude,
even for invalid or singular input matrices. -/
theorem inverse_coordinates_magnitude (A : Matrix (Fin d) (Fin d) ℤ) (x : Fin d → ℤ)
    (matrixBound vectorBound : ℕ) (positive : 1≤matrixBound)
    (ha : ∀ i j, (A i j).natAbs ≤ matrixBound) (hx : ∀ i, (x i).natAbs ≤ vectorBound)
    (i : Fin d) :
    ((InverseData.mk A.adjugate A.det).coordinates x i).natAbs ≤
      d*(d.factorial*matrixBound^d)*vectorBound := by
  exact (Int.natAbs_ediv_le_natAbs _ _).trans
    (mulVec_magnitude A.adjugate x _ _ (adjugate_magnitude A matrixBound positive ha) hx i)

/-- A uniform magnitude budget for decoding a neighboring cell. -/
def coordinateMagnitude (d bound : ℕ) : ℕ := d*(d.factorial*bound^d)*(2*bound+1)
def reconstructionMagnitude (d bound : ℕ) : ℕ := bound+d*bound*coordinateMagnitude d bound

/-- Bounds for every scalar in a decoder probe: the difference vector, the
adjugate product, quotient coordinates, and reconstructed physical point.
The query may be any point at distance at most one beyond the input bound. -/
theorem BasisData.probe_magnitudes {n : ℕ} (B : BasisData n d) (bound : ℕ) (positive : 1≤bound)
    (origin : ∀ v i, (B.origin v i).natAbs≤bound)
    (matrix : ∀ i j, (B.basis i j).natAbs≤bound)
    (x : Cell d) (query : ∀ i, (x i).natAbs≤bound+1) (v : Fin n) :
    (∀ i, ((x-B.origin v) i).natAbs≤2*bound+1) ∧
    (∀ i, (B.basis.adjugate.mulVec (x-B.origin v) i).natAbs≤coordinateMagnitude d bound) ∧
    (∀ i, (B.inverseData.coordinates (x-B.origin v) i).natAbs≤coordinateMagnitude d bound) ∧
    (∀ i, (B.realize (v,B.inverseData.coordinates (x-B.origin v)) i).natAbs≤reconstructionMagnitude d bound) := by
  have difference : ∀ i, ((x-B.origin v) i).natAbs≤2*bound+1 := by
    intro i
    exact (Int.natAbs_sub_le _ _).trans (by have := query i; have := origin v i; omega)
  have numerator := mulVec_magnitude B.basis.adjugate (x-B.origin v) _ _
    (adjugate_magnitude B.basis bound positive matrix) difference
  have coordinates := inverse_coordinates_magnitude B.basis (x-B.origin v) bound _ positive matrix difference
  refine ⟨difference,numerator,coordinates,fun i => ?_⟩
  have product := mulVec_magnitude B.basis (B.inverseData.coordinates (x-B.origin v)) bound
    (coordinateMagnitude d bound) matrix coordinates i
  exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add (origin v i) product)

/-- The entire reconstructed point has polynomial magnitude in the input
entry bound. The exponent depends only on dimension. -/
theorem reconstruction_polynomial (bound d : ℕ) :
    reconstructionMagnitude d bound ≤
      (1+3*d*d*d.factorial)*(bound+1)^(d+2) := by
  have powers : bound^d≤(bound+1)^d := Nat.pow_le_pow_left (Nat.le_succ bound) d
  have coordinates : coordinateMagnitude d bound ≤ 3*d*d.factorial*(bound+1)^(d+1) := by
    have h := Nat.mul_le_mul powers (show 2*bound+1≤3*(bound+1) by omega)
    have scaled := Nat.mul_le_mul_left (d*d.factorial) h
    simpa [coordinateMagnitude,pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using scaled
  have product := Nat.mul_le_mul (Nat.le_succ bound) coordinates
  have low : bound≤(bound+1)^(d+2) := by
    exact (Nat.le_succ bound).trans (by simpa using Nat.pow_le_pow_right (by omega : 1≤bound+1) (by omega : 1≤d+2))
  have high : d*bound*coordinateMagnitude d bound ≤ 3*d*d*d.factorial*(bound+1)^(d+2) := by
    simpa [pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using Nat.mul_le_mul_left d product
  unfold reconstructionMagnitude
  nlinarith

/-- Decoder values of polynomial magnitude in the input entries fit every
word size above a fixed-dimensional multiple of their binary length. This is
not a log(n) bound unless input entries are polynomially bounded in n. -/
theorem reconstruction_fits (bound d w : ℕ) (value : ℤ)
    (width : (Nat.log2 (1+3*d*d*d.factorial+1)+2*(d+2))*Nat.log2 (bound+2)+2≤w)
    (h : value.natAbs≤reconstructionMagnitude d bound) : ComplexityAbstract.RAM.Fits w value := by
  exact WordBounds.polynomial_fits_uniform _ _ _ w value width (h.trans (reconstruction_polynomial bound d))

/-- A bound on required decoder precision measured in input words. -/
def decoderWordFactor (d : ℕ) : ℕ := Nat.log2 (1+3*d*d*d.factorial+1)+2+3*(d+2)

/-- Word-sized period entries need only a dimension-dependent number of words
for the determinant. This is a precision bound; arithmetic routines are separate. -/
theorem BasisData.determinant_fits_words {n : ℕ} (B : BasisData n d) (w : ℕ) (positive : 0<w)
    (matrix : ∀ i j, ComplexityAbstract.RAM.Fits w (B.basis i j)) :
    ComplexityAbstract.RAM.Fits ((Nat.log2 (d.factorial+1)+2+3*d)*w) B.basis.det := by
  apply WordBounds.polynomial_fits_words d.factorial d w _ positive
  have h := determinant_magnitude B.basis (2^w) (fun i j => WordBounds.natAbs_le_of_fits (matrix i j))
  exact h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ _) d))

/-- A neighboring-cell query has magnitude at most one beyond its origin. -/
theorem BasisData.neighbor_magnitude {n : ℕ} (B : BasisData n d) (bound : ℕ)
    (origin : ∀ v i, (B.origin v i).natAbs≤bound) (v : Fin n) (direction i : Fin d) :
    ((B.origin v+unit direction) i).natAbs≤bound+1 := by
  have unitBound : (unit direction i).natAbs≤1 := by
    simp only [unit,Pi.single_apply]
    split <;> simp
  exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add (origin v i) unitBound)

/-- Word-sized input coordinates and periods give constant-word precision for
all quotient coordinates and reconstructed points in an actual neighbor probe.
The constant depends only on dimension, independently of the integer entries,
word size, representative count, and matrix nonsingularity. -/
theorem BasisData.neighbor_probe_fits_words {n : ℕ} (B : BasisData n d) (w : ℕ) (positive : 0<w)
    (origin : ∀ v i, ComplexityAbstract.RAM.Fits w (B.origin v i))
    (matrix : ∀ i j, ComplexityAbstract.RAM.Fits w (B.basis i j))
    (u v : Fin n) (direction : Fin d) :
    let z := B.inverseData.coordinates (B.origin u+unit direction-B.origin v)
    (∀ i, ComplexityAbstract.RAM.Fits (decoderWordFactor d*w) (z i)) ∧
      ∀ i, ComplexityAbstract.RAM.Fits (decoderWordFactor d*w) (B.realize (v,z) i) := by
  have boundPositive : 1≤(2:ℕ)^w := Nat.one_le_two_pow
  have origins := fun v i => WordBounds.natAbs_le_of_fits (origin v i)
  have matrices := fun i j => WordBounds.natAbs_le_of_fits (matrix i j)
  obtain ⟨_,_,coordinates,reconstruction⟩ := B.probe_magnitudes (2^w) boundPositive origins matrices
    (B.origin u+unit direction) (B.neighbor_magnitude _ origins u direction) v
  have precision (value : ℤ) (h : value.natAbs≤reconstructionMagnitude d (2^w)) :
      ComplexityAbstract.RAM.Fits (decoderWordFactor d*w) value :=
    WordBounds.polynomial_fits_words _ _ w value positive (h.trans (reconstruction_polynomial _ _))
  refine ⟨fun i => precision _ ((coordinates i).trans ?_),fun i => precision _ (reconstruction i)⟩
  have factor : 1≤d*2^w := Nat.mul_pos (by have := direction.isLt; omega) (by positivity)
  have scaled := Nat.mul_le_mul_right (coordinateMagnitude d (2^w)) factor
  have scaledBound : coordinateMagnitude d (2^w)≤d*2^w*coordinateMagnitude d (2^w) := by simpa using scaled
  exact scaledBound.trans (Nat.le_add_left _ (2^w))

end LeanTrominoes.Domino
