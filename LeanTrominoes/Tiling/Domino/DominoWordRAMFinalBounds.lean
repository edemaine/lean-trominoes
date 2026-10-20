/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMSizeBounds
import LeanTrominoes.Tiling.Domino.DominoWordRAMGlobalCandidate
import LeanTrominoes.Tiling.Domino.DominoWordRAMGlobalPrepareBounds

/-! # Uniform resource bounds for the complete domino decision program

The fixed dimension affects constants. Runtime is polynomial in the original
binary input size, and every arithmetic operand and allocated address fits a
logarithmic word. The conservative exponent includes cold matching memory.
-/
namespace LeanTrominoes.Domino.WordRAM.FinalBounds
open ComplexityAbstract.RAM
open Binary
variable {n d : ℕ}

noncomputable def candidateFactor (d : ℕ) : ℕ :=
  d*(100*Candidate.slotBound d+1000)+(9*d+25)*2^d+14
noncomputable def scanFactor (d : ℕ) : ℕ := d*(candidateFactor d+3)+3*d+7
noncomputable def scanCost (n d L : ℕ) : ℕ := n*(d*(n*(Driver.candidateCost d L+3)+3)+4)+3

 theorem candidate_bound (B : BasisData n d) :
    Driver.candidateCost d (precision B) ≤ candidateFactor d*(size B+1)^2 := by
  have length := (size_controls B).2.2
  have quadratic : (precision B+1)^2 ≤ (size B+1)^2 := Nat.pow_le_pow_left (by omega) 2
  have unit : 1 ≤ (size B+1)^2 := one_le_pow₀ (by omega)
  calc
    _=d*(100*Candidate.slotBound d+1000)*(precision B+1)^2+((9*d+25)*2^d+14) := by
      unfold Driver.candidateCost Candidate.coordinateCost
      ring
    _≤d*(100*Candidate.slotBound d+1000)*(size B+1)^2+((9*d+25)*2^d+14)*(size B+1)^2 := by
      exact Nat.add_le_add (Nat.mul_le_mul_left _ quadratic)
        (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left ((9*d+25)*2^d+14) unit)
    _=candidateFactor d*(size B+1)^2 := by unfold candidateFactor; ring

 theorem scan_bound (B : BasisData n d) :
    scanCost n d (precision B) ≤ scanFactor d*(size B+1)^4 := by
  have count := (size_controls B).1
  have countSquare : n*n ≤ (size B+1)^2 := by
    simpa only [pow_two] using Nat.pow_le_pow_left (show n ≤ size B+1 by omega) 2
  have unit2 : 1 ≤ (size B+1)^2 := one_le_pow₀ (by omega)
  have unit4 : 1 ≤ (size B+1)^4 := one_le_pow₀ (by omega)
  have count4 : n ≤ (size B+1)^4 := count.trans (by
    have grow := pow_le_pow_right₀ (by omega : 1 ≤ size B+1) (show 1 ≤ 4 by omega)
    simp only [pow_one] at grow
    omega)
  have candidate : Driver.candidateCost d (precision B)+3 ≤ (candidateFactor d+3)*(size B+1)^2 := by
    have main := candidate_bound B
    have extra := Nat.mul_le_mul_left 3 unit2
    nlinarith only [main,extra]
  calc
    _=n*n*d*(Driver.candidateCost d (precision B)+3)+n*(3*d+4)+3 := by unfold scanCost; ring
    _≤((size B+1)^2*d)*((candidateFactor d+3)*(size B+1)^2)+
        (size B+1)^4*(3*d+4)+3*(size B+1)^4 :=
      Nat.add_le_add (Nat.add_le_add
        (Nat.mul_le_mul (Nat.mul_le_mul_right d countSquare) candidate)
        (Nat.mul_le_mul_right _ count4)) (by simpa using Nat.mul_le_mul_left 3 unit4)
    _=scanFactor d*(size B+1)^4 := by unfold scanFactor; ring

noncomputable def timeFactor (d : ℕ) : ℕ :=
  GlobalPrepare128.timeCoefficient d+scanFactor d+18*(SizeBounds.edgeFactor d+1)+1000+SizeBounds.coldFactor d

noncomputable def totalCost (B : BasisData n d) : ℕ :=
  8+GlobalPrepare128.costBound B+17+scanCost n d (precision B)+18*SizeBounds.edgeCount n d+983+
    (4*(4*(BipartiteMatching.DenseWordRAM.size (SizeBounds.matchingInput B)+2)^8)+70+
      1000*(BipartiteMatching.DenseWordRAM.size (SizeBounds.matchingInput B)+1)^4)

 theorem total_bound (B : BasisData n d) : totalCost B ≤ timeFactor d*(size B+1)^16 := by
  have grow2 : (size B+1)^2 ≤ (size B+1)^16 := pow_le_pow_right₀ (by omega) (by omega)
  have grow4 : (size B+1)^4 ≤ (size B+1)^16 := pow_le_pow_right₀ (by omega) (by omega)
  have prep := (GlobalPrepare128.time_polynomial B).trans
    (Nat.mul_le_mul_left (GlobalPrepare128.timeCoefficient d) grow2)
  have scan := (scan_bound B).trans (Nat.mul_le_mul_left (scanFactor d) grow4)
  have edges := Nat.mul_le_mul_left 18 (SizeBounds.edgeCount_bound B 16 (by omega))
  have cold := SizeBounds.cold_runtime_bound B 0
  have unit : 1 ≤ (size B+1)^16 := one_le_pow₀ (by omega)
  have fixed := Nat.mul_le_mul_left 1000 unit
  simp only [Nat.mul_one,Nat.sub_zero] at cold fixed
  unfold totalCost timeFactor
  nlinarith only [prep,scan,edges,cold,fixed]

noncomputable def wordCoefficient (d : ℕ) : ℕ :=
  (Nat.log2 (GlobalPrepare128.resourceCoefficient d+1)+2)+
  (Nat.log2 (SizeBounds.operationWordFactor d+1)+6)+
  (Nat.log2 (SizeBounds.arenaFactor d+1)+32)+SizeBounds.matchingWordCoefficient d

 theorem word_bounds (B : BasisData n d) (w : ℕ)
    (width : wordCoefficient d*Nat.log2 (size B+2)+2 ≤ w) :
    Fits w (GlobalPrepare128.resourceBound B) ∧ Fits w (SizeBounds.operationBound B : ℕ) ∧
    Fits w (4*(BipartiteMatching.DenseWordRAM.size (SizeBounds.matchingInput B)+2)^8 : ℕ) ∧
    BipartiteMatching.DenseWordRAM.callWidth (SizeBounds.matchingInput B) ≤ w := by
  have component (a : ℕ) (small : a ≤ wordCoefficient d) : a*Nat.log2 (size B+2)+2 ≤ w :=
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ small) 2).trans width
  refine ⟨GlobalPrepare128.resource_fits B (component _ ?_),
    SizeBounds.operation_word_fits B w (component _ ?_),
    SizeBounds.arena_word_fits B w (component _ ?_),SizeBounds.matching_width B w (component _ ?_)⟩
  all_goals unfold wordCoefficient; omega

end LeanTrominoes.Domino.WordRAM.FinalBounds
