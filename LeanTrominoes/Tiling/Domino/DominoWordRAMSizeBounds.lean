/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMCandidate
import LeanTrominoes.Tiling.Domino.DominoWordRAMDeterminantSetup
import LeanTrominoes.Tiling.Domino.DominoWordRAMPaddedGraphMatching
import LeanTrominoes.Graphs.Matching.BipartiteMatchingWordRAMInvocation

/-! # Polynomial bounds in the honest original binary input size -/
namespace LeanTrominoes.Domino.WordRAM.SizeBounds
open Binary
variable {n d : ℕ}

def edgeFactor (d : ℕ) : ℕ := 2*d*2^d

def edgeCount (n d : ℕ) : ℕ := 2*n*n*d*2^d+1
noncomputable def matchingInput (B : BasisData n d) : BipartiteMatching.DenseWordRAM.Input :=
  ⟨n*2^d+1,n*2^d+1,PaddedGraph.edges B⟩

noncomputable def totalSpace (d : ℕ) : ℕ := ∑ direction : Fin d, Candidate.space direction
noncomputable def initialFactor (d : ℕ) : ℕ := DeterminantSetup.slots d+3+d
noncomputable def heap (B : BasisData n d) : ℕ :=
  Candidate.inputEnd B+initialFactor d*precision B+2*edgeCount n d+n*n*totalSpace d*precision B
noncomputable def heapFactor (d : ℕ) : ℕ := 1+initialFactor d+2*(edgeFactor d+1)+totalSpace d
noncomputable def wordFactor (d : ℕ) : ℕ := 20*(Candidate.slotBound d+5)*(heapFactor d+1)
def matchingFactor (d : ℕ) : ℕ := 2*2^d+edgeFactor d+4

theorem inputEnd_le (B : BasisData n d) : Candidate.inputEnd B≤ size B := by
  unfold Candidate.inputEnd size
  omega

theorem size_positive (B : BasisData n d) : 1≤ size B := by unfold size; omega

private theorem power_mono (size : ℕ) (exponent maximum : ℕ) (within : exponent≤ maximum) :
    size^exponent≤(size+1)^maximum :=
  (Nat.pow_le_pow_left (by omega : size≤ size+1) exponent).trans (pow_le_pow_right₀ (by omega : 1≤ size+1) within)

theorem edgeCount_bound (B : BasisData n d) (exponent : ℕ) (two : 2≤ exponent) :
    edgeCount n d≤(edgeFactor d+1)*(size B+1)^exponent := by
  have count := (size_controls B).1
  have square : n*n≤(size B+1)^exponent := by
    calc
      n*n≤(size B)^2 := by simpa only [pow_two] using Nat.pow_le_pow_left count 2
      _≤_ := power_mono _ _ _ two
  have product := Nat.mul_le_mul_left (edgeFactor d) square
  have unit : 1≤(size B+1)^exponent := one_le_pow₀ (by omega)
  unfold edgeCount edgeFactor at *
  nlinarith only [product,unit]

theorem heap_bound (B : BasisData n d) : heap B≤ heapFactor d*(size B+1)^3 := by
  have count := (size_controls B).1
  have length := (size_controls B).2.2
  have endpoint := inputEnd_le B
  have countSquare : n*n≤(size B+1)^2 := by
    have h := Nat.pow_le_pow_left (show n≤ size B+1 by omega) 2
    simpa only [pow_two] using h
  have lengthCube : precision B≤(size B+1)^3 := length.trans (by exact (show size B≤(size B+1)^3 from by simpa using power_mono (size B) 1 3 (by omega)))
  have endpointCube : Candidate.inputEnd B≤(size B+1)^3 := endpoint.trans (by simpa using power_mono (size B) 1 3 (by omega))
  have mixed : n*n*precision B≤(size B+1)^3 := by
    have h := Nat.mul_le_mul countSquare (show precision B≤ size B+1 by omega)
    simpa only [pow_succ] using h
  have initial := Nat.mul_le_mul_left (initialFactor d) lengthCube
  have copies := Nat.mul_le_mul_left (totalSpace d) mixed
  have edges := edgeCount_bound B 3 (by omega)
  unfold heap heapFactor
  nlinarith only [endpointCube,initial,copies,edges]

theorem word_bound (B : BasisData n d) :
    FreshProbe.scalarBound (Candidate.slotBound d) (heap B)≤ wordFactor d*(size B+1)^3 := by
  have h := heap_bound B
  have unit : 1≤(size B+1)^3 := one_le_pow₀ (by omega)
  have upper : heap B+1≤(heapFactor d+1)*(size B+1)^3 := by nlinarith only [h,unit]
  have mul := Nat.mul_le_mul_left (20*(Candidate.slotBound d+5)) upper
  simpa only [FreshProbe.scalarBound,wordFactor,Nat.mul_assoc] using mul

theorem matching_size_bound (B : BasisData n d) :
    BipartiteMatching.DenseWordRAM.size (matchingInput B)≤ matchingFactor d*(size B+1)^2 := by
  have vertices : n≤(size B+1)^2 := (size_controls B).1.trans (by simpa using power_mono (size B) 1 2 (by omega))
  have product := Nat.mul_le_mul_left (2*2^d) vertices
  have edges := edgeCount_bound B 2 (by omega)
  have unit : 1≤(size B+1)^2 := one_le_pow₀ (by omega)
  unfold BipartiteMatching.DenseWordRAM.size matchingInput
  rw [PaddedGraph.edges_length]
  unfold matchingFactor edgeCount at *
  nlinarith only [product,edges,unit]


noncomputable def uniformSpace (d : ℕ) : ℕ := d*d*(Candidate.slotBound d+3)
noncomputable def driverHeap (B : BasisData n d) : ℕ :=
  Candidate.inputEnd B+initialFactor d*precision B+2*edgeCount n d+n*n*uniformSpace d*precision B
noncomputable def driverHeapFactor (d : ℕ) : ℕ := 1+initialFactor d+2*(edgeFactor d+1)+uniformSpace d
noncomputable def driverWordFactor (d : ℕ) : ℕ := 20*(Candidate.slotBound d+5)*(driverHeapFactor d+1)

theorem driver_heap_bound (B : BasisData n d) : driverHeap B≤ driverHeapFactor d*(size B+1)^3 := by
  have count := (size_controls B).1
  have length := (size_controls B).2.2
  have endpoint := inputEnd_le B
  have countSquare : n*n≤(size B+1)^2 := by
    have h := Nat.pow_le_pow_left (show n≤ size B+1 by omega) 2
    simpa only [pow_two] using h
  have lengthCube : precision B≤(size B+1)^3 := length.trans (by exact (show size B≤(size B+1)^3 from by simpa using power_mono (size B) 1 3 (by omega)))
  have endpointCube : Candidate.inputEnd B≤(size B+1)^3 := endpoint.trans (by simpa using power_mono (size B) 1 3 (by omega))
  have mixed : n*n*precision B≤(size B+1)^3 := by
    have h := Nat.mul_le_mul countSquare (show precision B≤ size B+1 by omega)
    simpa only [pow_succ] using h
  have initial := Nat.mul_le_mul_left (initialFactor d) lengthCube
  have copies := Nat.mul_le_mul_left (uniformSpace d) mixed
  have edges := edgeCount_bound B 3 (by omega)
  unfold driverHeap driverHeapFactor
  nlinarith only [endpointCube,initial,copies,edges]

theorem driver_word_bound (B : BasisData n d) :
    FreshProbe.scalarBound (Candidate.slotBound d) (driverHeap B)≤ driverWordFactor d*(size B+1)^3 := by
  have h := driver_heap_bound B
  have unit : 1≤(size B+1)^3 := one_le_pow₀ (by omega)
  have upper : driverHeap B+1≤(driverHeapFactor d+1)*(size B+1)^3 := by nlinarith only [h,unit]
  have mul := Nat.mul_le_mul_left (20*(Candidate.slotBound d+5)) upper
  simpa only [FreshProbe.scalarBound,driverWordFactor,Nat.mul_assoc] using mul

def arenaFactor (d : ℕ) : ℕ := 4*(matchingFactor d+2)^8
def coldFactor (d : ℕ) : ℕ := 4*arenaFactor d+70+1000*(matchingFactor d+1)^4

theorem matching_size_add (B : BasisData n d) (offset : ℕ) :
    BipartiteMatching.DenseWordRAM.size (matchingInput B)+offset≤(matchingFactor d+offset)*(size B+1)^2 := by
  have bound := matching_size_bound B
  have unit : 1≤(size B+1)^2 := one_le_pow₀ (by omega)
  have extra := Nat.mul_le_mul_left offset unit
  nlinarith only [bound,extra]

theorem arena_bound (B : BasisData n d) :
    4*(BipartiteMatching.DenseWordRAM.size (matchingInput B)+2)^8≤ arenaFactor d*(size B+1)^16 := by
  have power := Nat.pow_le_pow_left (matching_size_add B 2) 8
  have multiply := Nat.mul_le_mul_left 4 power
  simpa only [arenaFactor,mul_pow,←pow_mul,Nat.mul_assoc] using multiply

theorem cold_runtime_bound (B : BasisData n d) (start : ℕ) :
    4*(4*(BipartiteMatching.DenseWordRAM.size (matchingInput B)+2)^8-start)+70+
      1000*(BipartiteMatching.DenseWordRAM.size (matchingInput B)+1)^4≤ coldFactor d*(size B+1)^16 := by
  have arena := arena_bound B
  have sub := Nat.sub_le (4*(BipartiteMatching.DenseWordRAM.size (matchingInput B)+2)^8) start
  have fourth := Nat.pow_le_pow_left (matching_size_add B 1) 4
  have fourth' : (BipartiteMatching.DenseWordRAM.size (matchingInput B)+1)^4≤
      (matchingFactor d+1)^4*(size B+1)^8 := by simpa only [mul_pow,←pow_mul] using fourth
  have grow : (size B+1)^8≤(size B+1)^16 := pow_le_pow_right₀ (by omega) (by omega)
  have larger := Nat.mul_le_mul_left ((matchingFactor d+1)^4) grow
  have unit : 1≤(size B+1)^16 := one_le_pow₀ (by omega)
  unfold coldFactor
  nlinarith only [arena,sub,fourth',larger,unit]

theorem heap_word_fits (B : BasisData n d) (w : ℕ)
    (width : (Nat.log2 (wordFactor d+1)+6)*Nat.log2 (size B+2)+2≤ w) :
    ComplexityAbstract.RAM.Fits w (FreshProbe.scalarBound (Candidate.slotBound d) (heap B) : ℕ) := by
  apply LeanTrominoes.WordBounds.polynomial_fits_uniform (wordFactor d) 3 (size B) w _ width
  simpa only [Int.natAbs_natCast] using word_bound B

theorem arena_word_fits (B : BasisData n d) (w : ℕ)
    (width : (Nat.log2 (arenaFactor d+1)+32)*Nat.log2 (size B+2)+2≤ w) :
    ComplexityAbstract.RAM.Fits w (4*(BipartiteMatching.DenseWordRAM.size (matchingInput B)+2)^8 : ℕ) := by
  apply LeanTrominoes.WordBounds.polynomial_fits_uniform (arenaFactor d) 16 (size B) w _ width
  simpa only [Int.natAbs_natCast] using arena_bound B

theorem driver_heap_word_fits (B : BasisData n d) (w : ℕ)
    (width : (Nat.log2 (driverWordFactor d+1)+6)*Nat.log2 (size B+2)+2≤ w) :
    ComplexityAbstract.RAM.Fits w (FreshProbe.scalarBound (Candidate.slotBound d) (driverHeap B) : ℕ) := by
  apply LeanTrominoes.WordBounds.polynomial_fits_uniform (driverWordFactor d) 3 (size B) w _ width
  simpa only [Int.natAbs_natCast] using driver_word_bound B


noncomputable def operationBound (B : BasisData n d) : ℕ :=
  FreshProbe.scalarBound (Candidate.slotBound d) (driverHeap B)+(n+1)*2^d+d+4
noncomputable def operationWordFactor (d : ℕ) : ℕ := driverWordFactor d+2^d+d+4

theorem operation_bound (B : BasisData n d) : operationBound B≤ operationWordFactor d*(size B+1)^3 := by
  have word := driver_word_bound B
  have grow : n+1≤(size B+1)^3 := by
    have count := (size_controls B).1
    have power : size B+1≤(size B+1)^3 := by simpa only [pow_one] using pow_le_pow_right₀ (by omega : 1≤ size B+1) (show 1≤3 by omega)
    exact (Nat.add_le_add_right count 1).trans power
  have vertices := Nat.mul_le_mul_right (2^d) grow
  have unit : 1≤(size B+1)^3 := one_le_pow₀ (by omega)
  have constants := Nat.mul_le_mul_left (d+4) unit
  unfold operationBound operationWordFactor
  nlinarith only [word,vertices,constants]

theorem operation_word_fits (B : BasisData n d) (w : ℕ)
    (width : (Nat.log2 (operationWordFactor d+1)+6)*Nat.log2 (size B+2)+2≤ w) :
    ComplexityAbstract.RAM.Fits w (operationBound B : ℕ) := by
  apply LeanTrominoes.WordBounds.polynomial_fits_uniform (operationWordFactor d) 3 (size B) w _ width
  simpa only [Int.natAbs_natCast] using operation_bound B


def matchingWordCoefficient (d : ℕ) : ℕ := 8*(Nat.log2 (matchingFactor d+3)+6)

theorem matching_width (B : BasisData n d) (w : ℕ)
    (width : matchingWordCoefficient d*Nat.log2 (size B+2)+2≤ w) :
    BipartiteMatching.DenseWordRAM.callWidth (matchingInput B)≤ w := by
  let m := BipartiteMatching.DenseWordRAM.size (matchingInput B)
  let coefficient := matchingFactor d+2
  let ell := Nat.log2 (size B+2)
  have magnitude : ((m+2 : ℕ) : ℤ).natAbs≤ coefficient*(size B+1)^2 := by
    simpa only [Int.natAbs_natCast] using matching_size_add B 2
  have fits := LeanTrominoes.WordBounds.polynomial_fits coefficient 2 (size B) (m+2 : ℕ) magnitude
  have upper : m+2<2^(Nat.log2 (coefficient+1)+2+2*(Nat.log2 (size B+1)+1)-1) := by
    exact_mod_cast fits.2.2
  have logarithm : Nat.log2 (m+2)< Nat.log2 (coefficient+1)+2+2*(Nat.log2 (size B+1)+1)-1 := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_lt_of_lt_pow (by omega : m+2≠0) upper
  have ellPositive : 1≤ ell := by
    have bound := Nat.log_mono_right (b:=2) (show 2≤ size B+2 by omega)
    simpa [ell,←Nat.log2_eq_log_two] using bound
  have smaller : Nat.log2 (size B+1)≤ ell := by
    simpa only [ell,Nat.log2_eq_log_two] using Nat.log_mono_right (b:=2) (show size B+1≤ size B+2 by omega)
  have constant := Nat.mul_le_mul_left (Nat.log2 (coefficient+1)+4) ellPositive
  have logle := (Nat.le_of_lt logarithm).trans (Nat.sub_le _ 1)
  have compressed : Nat.log2 (m+2)≤(Nat.log2 (coefficient+1)+6)*ell := by nlinarith only [logle,smaller,constant]
  change 8*Nat.log2 (m+2)+2≤ w
  unfold matchingWordCoefficient at width
  change 8*(Nat.log2 (coefficient+1)+6)*ell+2≤ w at width
  nlinarith only [width,compressed]

end LeanTrominoes.Domino.WordRAM.SizeBounds
