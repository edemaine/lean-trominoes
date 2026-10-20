/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATCellEvaluation

/-! # Arithmetic generation of the actual periodic-cover edges -/
namespace LeanTrominoes.PeriodicTwoSAT.WordRAM
open PeriodicLatticeGraph ImplicationGraph.TwoSATExpression
variable {d M : ℕ} [NeZero M]

namespace Raw

theorem recordAt_original (raw : Input d) (i : ℕ) (inside : i < raw.2.length) :
    recordAt raw i = raw.2[i] := by
  have index : (recordIndex raw i).val = i := by
    simp only [recordIndex, ← Int.natCast_emod, Int.toNat_natCast]
    exact Nat.mod_eq_of_lt (by omega)
  simp only [recordAt,index,records]
  exact List.getElem_append_left (by omega)

end Raw

private theorem coverIndex_row {n : ℕ} (a : Signed (Fin n)) (i : Fin (M^d)) :
    (coverIndex n d M (a,(coordinateIndex d M).symm i)).val =
      (literalIndex n a).val*M^d+i.val := by
  simp only [coverIndex,Equiv.trans_apply,Equiv.prodCongr_apply,Prod.map_fst,Prod.map_snd,
    finProdFinEquiv_apply_val,Equiv.apply_symm_apply]
  ring

private theorem shiftedCoordinate_cast (i : Fin (M^d)) (offset : Lattice d) :
    (shiftedCoordinate d M i.val offset : ℤ) = ∑ j : Fin d,
      (((i.val : ℤ)/(M : ℤ)^j.val%(M : ℤ)+offset j)%(M : ℤ))*(M : ℤ)^j.val := by
  simp only [shiftedCoordinate,Nat.cast_sum,Nat.cast_mul,Nat.cast_pow]
  apply Finset.sum_congr rfl
  intro j _
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast NeZero.ne M))]
  simp only [Int.natCast_emod,Int.natCast_ediv,Nat.cast_pow]

namespace Cells

theorem activeEdge_fields (raw : Raw.Input d) (e : Expression) (env : Fin 17 → ℤ) (memory : ℕ → ℤ)
    (clauseCount : env 7 = raw.2.length) (periodValue : env 8 = M) (coordinateCount : env 9 = M^d)
    (i : Fin (M^d*(raw.2.length*2))) (edgeValue : e.eval env memory = i.val) :
    (row e).eval env memory = (i.val/(raw.2.length*2) : ℕ) ∧
    (clauseIndex e).eval env memory = (i.val%(raw.2.length*2)/2 : ℕ) ∧
    (direction e).eval env memory = (i.val%2 : ℕ) := by
  have rowSmall : i.val/(raw.2.length*2) < M^d :=
    Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using i.isLt)
  simp only [row,clauseIndex,direction,mod_eval,div_eval,two,mul_eval,constant_eval,input_eval,
    clauseCount,coordinateCount,edgeValue]
  norm_cast
  simp only [Nat.mul_comm 2 raw.2.length,Nat.mod_eq_of_lt rowSmall,and_self]

theorem sourceVertex_active (raw : Raw.Input d) (sourceBase : ℕ) (env : Fin 17 → ℤ) (memory : ℕ → ℤ)
    (source : Raw.SourceAt raw sourceBase memory) (baseValue : env 5 = sourceBase)
    (clauseCount : env 7 = raw.2.length) (periodValue : env 8 = M) (coordinateCount : env 9 = M^d)
    (e : Expression) (i : Fin (M^d*(raw.2.length*2))) (edgeValue : e.eval env memory = i.val) :
    (sourceVertex d e).eval env memory =
      ((paddedEdgeAt (by omega) (liftFormula raw.2) M
        ⟨i.val,by simpa [liftFormula] using i.isLt⟩).1.val : ℤ) := by
  have fields := activeEdge_fields raw e env memory clauseCount periodValue coordinateCount i edgeValue
  have nonempty : 0 < raw.2.length := by
    have bound := i.isLt
    by_contra h
    have zero : raw.2.length = 0 := by omega
    simp [zero] at bound
  have clauseSmall : i.val%(raw.2.length*2)/2 < raw.2.length :=
    Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using Nat.mod_lt i.val (by omega : 0 < raw.2.length*2))
  have directionValue : (i.val%(raw.2.length*2))%2 = i.val%2 := Nat.mod_mod_of_dvd _ (by simp)
  rw [sourceVertex_eval raw sourceBase env memory source baseValue clauseCount e,fields.1,fields.2.1,fields.2.2,
    Raw.recordAt_original raw _ clauseSmall,coordinateCount]
  dsimp only [paddedEdgeAt,liftFormula]
  simp only [List.length_map,List.getElem_map]
  rw [coverIndex_row]
  push_cast
  rw [paddedArcAt_sourceField]
  simp only [directionValue,Int.natCast_emod,Nat.cast_ofNat]

 theorem targetVertex_active (raw : Raw.Input d) (sourceBase : ℕ) (env : Fin 17 → ℤ) (memory : ℕ → ℤ)
    (source : Raw.SourceAt raw sourceBase memory) (baseValue : env 5 = sourceBase)
    (clauseCount : env 7 = raw.2.length) (periodValue : env 8 = M) (coordinateCount : env 9 = M^d)
    (e : Expression) (i : Fin (M^d*(raw.2.length*2))) (edgeValue : e.eval env memory = i.val) :
    (targetVertex d e).eval env memory =
      ((paddedEdgeAt (by omega) (liftFormula raw.2) M
        ⟨i.val,by simpa [liftFormula] using i.isLt⟩).2.val : ℤ) := by
  have fields := activeEdge_fields raw e env memory clauseCount periodValue coordinateCount i edgeValue
  have nonempty : 0 < raw.2.length := by
    have bound := i.isLt
    by_contra h
    have zero : raw.2.length = 0 := by omega
    simp [zero] at bound
  have clauseSmall : i.val%(raw.2.length*2)/2 < raw.2.length :=
    Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using Nat.mod_lt i.val (by omega : 0 < raw.2.length*2))
  have directionValue : (i.val%(raw.2.length*2))%2 = i.val%2 := Nat.mod_mod_of_dvd _ (by simp)
  rw [targetVertex_eval raw sourceBase env memory source baseValue clauseCount e,fields.1,fields.2.1,fields.2.2,
    Raw.recordAt_original raw _ clauseSmall,coordinateCount]
  dsimp only [paddedEdgeAt,liftFormula]
  simp only [List.length_map,List.getElem_map]
  rw [shifted_coverIndex,← literalIndex_value]
  push_cast
  rw [paddedArcAt_targetField]
  simp only [shiftedCoordinate,Nat.cast_sum,Nat.cast_mul,Nat.cast_pow]
  have castMod (x : ℤ) : ((x%(M : ℤ)).toNat : ℤ) = x%(M : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg x (by exact_mod_cast NeZero.ne M))
  simp_rw [paddedArcAt_offsetField,castMod]
  simp only [periodValue,directionValue,Int.natCast_emod,Int.natCast_ediv,Nat.cast_pow,Nat.cast_mul,Nat.cast_ofNat,Fin.val_mk]

end Cells
end LeanTrominoes.PeriodicTwoSAT.WordRAM
