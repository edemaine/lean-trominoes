/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATHeaderBounds
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATCellCorrectness
import LeanTrominoes.Computation.Compiler.FiniteTwoSATInvocation
import LeanTrominoes.Computation.RAM.PolynomialBounds

/-! # The constructed header agrees with the finite Horn specification -/
namespace LeanTrominoes.PeriodicTwoSAT.WordRAM.Header
open ImplicationGraph.TwoSATExpression ComplexityAbstract.RAM
variable {d : ℕ}

theorem environment_metadata (raw : Raw.Input d) :
    Cells.Metadata raw (Cells.tablePeriod raw) (environment d raw.1 raw.2.length) := by
  refine ⟨rfl,rfl,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change (period d raw.1 : ℤ) = Cells.tablePeriod raw
    rw [period_eq]
  · change (coordinateCount d raw.1 : ℤ) = (Cells.tablePeriod raw : ℤ)^d
    simp only [coordinateCount,period_eq,Nat.cast_pow]
  · change (vertexCount d raw.1 : ℤ) = (raw.1+1 : ℤ)*2*(Cells.tablePeriod raw : ℤ)^d
    simp only [vertexCount,coordinateCount,period_eq,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,Nat.cast_pow]
  · change (edgeCount d raw.1 raw.2.length : ℤ) = (Cells.tablePeriod raw : ℤ)^d*(raw.2.length*2 : ℤ)
    simp only [edgeCount,coordinateCount,period_eq,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow]
  · change (atomCount d raw.1 : ℤ) = (raw.1 : ℤ)*2*((raw.1+1 : ℤ)*2*(Cells.tablePeriod raw : ℤ)^d)+1
    simp only [atomCount,vertexCount,coordinateCount,period_eq,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,Nat.cast_pow]
  · change (ruleCount d raw.1 raw.2.length : ℤ) = 3*(raw.1 : ℤ)+2*raw.1*((Cells.tablePeriod raw : ℤ)^d*(raw.2.length*2 : ℤ))+raw.2.length
    simp only [ruleCount,edgeCount,coordinateCount,period_eq,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_pow]
  · change (occurrenceCount d raw.1 raw.2.length : ℤ) = 2*(raw.1 : ℤ)+2*raw.1*((Cells.tablePeriod raw : ℤ)^d*(raw.2.length*2 : ℤ))
    simp only [occurrenceCount,edgeCount,coordinateCount,period_eq,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_pow]
  · change (length d raw.1 raw.2.length : ℤ) =
      4+(3*(raw.1 : ℤ)+2*raw.1*((Cells.tablePeriod raw : ℤ)^d*(raw.2.length*2 : ℤ))+raw.2.length)+
        2*(2*(raw.1 : ℤ)+2*raw.1*((Cells.tablePeriod raw : ℤ)^d*(raw.2.length*2 : ℤ)))
    simp only [length,ruleCount,occurrenceCount,edgeCount,coordinateCount,period_eq,
      Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_pow]


theorem size_uniform (raw : Raw.Input d) :
    size d raw.1 raw.2.length=Horn.WordRAM.size (uniformInput raw.2) := by
  rw [uniformInput_size]
  simp only [size,atomCount,vertexCount,coordinateCount,ruleCount,occurrenceCount,edgeCount,period_eq]
  ring


theorem length_fullWords (raw : Raw.Input d) :
    length d raw.1 raw.2.length=(Cells.fullWords raw).length := by
  rw [Cells.fullWords_length,Cells.headWords_length,Cells.atomWords_length]
  simp only [length,ruleCount,occurrenceCount,edgeCount,coordinateCount,period_eq,
    Cells.tableEdges,Cells.tablePeriod,Cells.edgeList_length]


private theorem arena_linear (d n m : ℕ) :
    4*(Raw.recordSize d+1)*(size d n m+bound d n+coordinateCount d n+n+3*m+4)≤arena d n m := by
  unfold arena
  apply Nat.mul_le_mul_left
  have basePositive : 1≤size d n m+bound d n+coordinateCount d n+n+3*m+4 := by omega
  simpa only [pow_one] using Nat.pow_le_pow_right basePositive (show 1≤27 by decide)


theorem length_le_arena (d n m : ℕ) : length d n m≤arena d n m := by
  have h := arena_linear d n m
  have target : length d n m≤4*(size d n m+bound d n+coordinateCount d n+n+3*m+4) := by
    dsimp [length,size]
    omega
  have factor : 4*(size d n m+bound d n+coordinateCount d n+n+3*m+4)≤
      4*(Raw.recordSize d+1)*(size d n m+bound d n+coordinateCount d n+n+3*m+4) := by nlinarith
  exact target.trans (factor.trans h)


theorem rawLength_lt_arena (raw : Raw.Input d) :
    (Raw.words raw).length<arena d raw.1 raw.2.length := by
  rw [Raw.words_length]
  have h := arena_linear d raw.1 raw.2.length
  have high : raw.2.length+1≤size d raw.1 raw.2.length+bound d raw.1+
      coordinateCount d raw.1+raw.1+3*raw.2.length+4 := by omega
  have product := Nat.mul_le_mul_left (4*(Raw.recordSize d+1)) high
  nlinarith

/-- The caller's high arena starts above the entire address range touched by
Horn at its certified small width. This proves its frame condition. -/

theorem arena_hornWidth (raw : Raw.Input d) :
    2^hornWidth (uniformInput raw.2)≤arena d raw.1 raw.2.length := by
  rw [hornWidth,← size_uniform raw]
  have logBound : 2^Nat.log2 (size d raw.1 raw.2.length+2)≤size d raw.1 raw.2.length+2 := by
    simpa only [Nat.log2_eq_log_two] using Nat.pow_log_le_self 2 (by omega : size d raw.1 raw.2.length+2≠0)
  have first := Nat.pow_le_pow_left logBound 27
  have second := Nat.pow_le_pow_left (show size d raw.1 raw.2.length+2≤
      size d raw.1 raw.2.length+bound d raw.1+coordinateCount d raw.1+raw.1+3*raw.2.length+4 by omega) 27
  have factor := Nat.mul_le_mul_left 4 (first.trans second)
  have coefficient : 4 ≤ 4*(Raw.recordSize d+1) := by omega
  have product := Nat.mul_le_mul_right
    ((size d raw.1 raw.2.length+bound d raw.1+coordinateCount d raw.1+raw.1+3*raw.2.length+4)^27) coefficient
  have exponentEq : 2^(27*Nat.log2 (size d raw.1 raw.2.length+2)+2)=
      4*(2^Nat.log2 (size d raw.1 raw.2.length+2))^27 := by
    rw [Nat.mul_comm 27,pow_add,pow_mul]
    ring
  rw [exponentEq]
  exact factor.trans product


theorem tableBase_parameters (d n m : ℕ) :
    ∀ i : Fin 17, 5 ≤ i.val → (environment d n m i).natAbs≤tableBase d n m := by
  intro i hi
  fin_cases i <;> dsimp [environment] at *
  all_goals unfold tableBase
  all_goals omega


theorem tableBase_aux (d n m : ℕ) : Raw.recordSize d≤tableBase d n m ∧
    n+1≤tableBase d n m ∧ length d n m≤tableBase d n m ∧ 1≤tableBase d n m := by
  unfold tableBase
  omega

/-- Fitting the arena also suffices for the width needed by the Horn call. -/

theorem hornWidth_le_of_arena_fits {d w : ℕ} (raw : Raw.Input d)
    (word : Fits w (arena d raw.1 raw.2.length : ℕ)) :
    ImplicationGraph.TwoSATExpression.hornWidth (uniformInput raw.2)≤w := by
  have address : arena d raw.1 raw.2.length < 2^w := by exact_mod_cast Allocation.nat_address word
  have powers : 2^hornWidth (uniformInput raw.2) < 2^w := (arena_hornWidth raw).trans_lt address
  exact ((Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp powers).le

end LeanTrominoes.PeriodicTwoSAT.WordRAM.Header
