/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMDigits
import LeanTrominoes.Tiling.Domino.PeriodicDominoWordBounds

/-! # Original integer input in binary

The input consists only of the number of representatives, precision metadata,
period-matrix entries, and representative coordinates. All integers are raw
little-endian bits with common sign-extension precision. No inverse, decoded
neighbor table, cover graph, matching, or answer is supplied by the encoding.
-/
namespace LeanTrominoes.Domino.WordRAM
open ComplexityAbstract.RAM
variable {n d : ℕ}

/-- A canonical logarithmic entry budget. Taking a sum instead of a maximum
changes bit length by at most the logarithm of the number of input entries. -/
def inputMagnitude (B : BasisData n d) : ℕ :=
  1+(∑ i, ∑ j, (B.basis i j).natAbs)+(∑ v, ∑ i, (B.origin v i).natAbs)

def entryBits (B : BasisData n d) : ℕ := LeanTrominoes.WordBounds.bits (inputMagnitude B)

def determinantWordFactor (d : ℕ) : ℕ := Nat.log2 (d.factorial+1)+2+3*d

def corePrecision (B : BasisData n d) : ℕ :=
  (decoderWordFactor d+determinantWordFactor d)*entryBits B

/-- Four guard bits permit absolute determinant doubling and the shift before
a long-remainder comparison, independently of the machine word size. -/
def precision (B : BasisData n d) : ℕ := corePrecision B+4

theorem basis_magnitude (B : BasisData n d) (i j : Fin d) :
    (B.basis i j).natAbs≤ inputMagnitude B := by
  have inner := Finset.single_le_sum (s := Finset.univ) (f := fun j => (B.basis i j).natAbs)
    (fun j _ => Nat.zero_le _) (Finset.mem_univ j)
  have outer := Finset.single_le_sum (s := Finset.univ) (f := fun i => ∑ j, (B.basis i j).natAbs)
    (fun i _ => Nat.zero_le _) (Finset.mem_univ i)
  unfold inputMagnitude
  omega

theorem origin_magnitude (B : BasisData n d) (v : Fin n) (i : Fin d) :
    (B.origin v i).natAbs≤ inputMagnitude B := by
  have inner := Finset.single_le_sum (s := Finset.univ) (f := fun i => (B.origin v i).natAbs)
    (fun i _ => Nat.zero_le _) (Finset.mem_univ i)
  have outer := Finset.single_le_sum (s := Finset.univ) (f := fun v => ∑ i, (B.origin v i).natAbs)
    (fun v _ => Nat.zero_le _) (Finset.mem_univ v)
  unfold inputMagnitude
  omega

theorem entryBits_positive (B : BasisData n d) : 0< entryBits B := by
  simp only [entryBits,LeanTrominoes.WordBounds.bits]
  omega

theorem basis_fits (B : BasisData n d) (i j : Fin d) : Fits (entryBits B) (B.basis i j) :=
  LeanTrominoes.WordBounds.fits_of_natAbs_le _ _ (basis_magnitude B i j)

theorem origin_fits (B : BasisData n d) (v : Fin n) (i : Fin d) : Fits (entryBits B) (B.origin v i) :=
  LeanTrominoes.WordBounds.fits_of_natAbs_le _ _ (origin_magnitude B v i)

theorem precision_positive (B : BasisData n d) : 0< precision B := by simp [precision]

/-- Raw field order is the fixed row-major period matrix, then the row-major
list of representative coordinate vectors. -/
def fields (B : BasisData n d) : List ℤ :=
  (List.finRange d).flatMap (fun i => (List.finRange d).map (fun j => B.basis i j)) ++
  (List.finRange n).flatMap (fun v => (List.finRange d).map (fun i => B.origin v i))

theorem fields_length (B : BasisData n d) : (fields B).length=d*d+n*d := by
  simp [fields,List.length_flatMap]

def words (B : BasisData n d) : List ℤ :=
  [(n:ℤ),(entryBits B:ℤ),(precision B:ℤ)] ++
    (fields B).flatMap (fun z => (Binary.integerDigits (precision B) z).map Int.ofNat)

/-- Size counts representatives and raw integer bit length, including the
canonical precision header. For fixed dimension, this is polynomially related
to the usual bit encoding of the original finite presentation. -/
def size (B : BasisData n d) : ℕ := n+entryBits B+precision B+(words B).length+1

theorem words_length (B : BasisData n d) : (words B).length=3+(d*d+n*d)*precision B := by
  simp [words,Binary.integerDigits,List.length_flatMap,fields_length]
  omega

theorem size_controls (B : BasisData n d) : n≤ size B ∧ entryBits B≤ size B ∧ precision B≤ size B := by
  unfold size
  omega

theorem determinant_fits (B : BasisData n d) : Fits (corePrecision B) B.basis.det := by
  have bound := B.determinant_fits_words (entryBits B) (entryBits_positive B) (basis_fits B)
  apply LeanTrominoes.WordBounds.fits_mono (fits := bound)
  unfold corePrecision determinantWordFactor
  nlinarith

/-- The common bit precision provides ample guard space above twice the
absolute determinant, as required by the binary remainder kernel. -/
theorem determinant_guard (B : BasisData n d) : 2*(2*B.basis.det.natAbs)≤2^(precision B) := by
  have bound := LeanTrominoes.WordBounds.natAbs_le_of_fits (determinant_fits B)
  simp only [precision,pow_add]
  norm_num
  nlinarith [Nat.zero_le ((2:ℕ)^corePrecision B)]

end LeanTrominoes.Domino.WordRAM
