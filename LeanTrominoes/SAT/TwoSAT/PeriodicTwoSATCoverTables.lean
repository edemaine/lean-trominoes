/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATLiftedInput
import LeanTrominoes.Computation.Compiler.FiniteTwoSATBatchTables

/-! # Dense quotient/remainder lookup in the padded periodic cover -/
namespace LeanTrominoes.PeriodicTwoSAT.WordRAM
open PeriodicLatticeGraph ImplicationGraph
variable {n d M : ℕ} [NeZero M]

def paddedArcAt (positive : 0<n) (c : Clause (Fin n) d) (direction : Fin 2) : Arc (Signed (Fin n)) d :=
  match c with
  | none => dummyArc positive d
  | some (a,b) => if direction.val=0 then ⟨negate a.1,b.1,b.2-a.2⟩ else ⟨negate b.1,a.1,a.2-b.2⟩

theorem paddedClauseArcs_ofFn (positive : 0<n) (c : Clause (Fin n) d) :
    paddedClauseArcs positive c=List.ofFn (paddedArcAt positive c) := by
  cases c with
  | none => simp [List.ofFn_succ,paddedClauseArcs,paddedArcAt]
  | some pair => rcases pair with ⟨a,b⟩; simp [List.ofFn_succ,paddedClauseArcs,paddedArcAt,clauseArcs]

private theorem flatMap_as_flatten {V W : Type} (xs : List V) (f : V → List W) :
    xs.flatMap f=(xs.map f).flatten := by induction xs <;> simp_all

theorem paddedArcs_ofFn (positive : 0<n) (f : Formula (Fin n) d) :
    paddedArcs positive f=List.ofFn (fun i : Fin (f.length*2) =>
      paddedArcAt positive f[i.val/2] ⟨i.val%2,by omega⟩) := by
  have blocks := TwoSATBatch.flatten_ofFn_blocks
    (fun i : Fin f.length => paddedArcAt positive f[i.val])
  have flattened : paddedArcs positive f=
      (List.ofFn fun i : Fin f.length => List.ofFn (paddedArcAt positive f[i.val])).flatten := by
    rw [List.ofFn_getElem_eq_map f (fun c => List.ofFn (paddedArcAt positive c))]
    simp_rw [← paddedClauseArcs_ofFn]
    exact flatMap_as_flatten f _
  exact flattened.trans blocks

def paddedEdgeAt (positive : 0<n) (f : Formula (Fin n) d) (M : ℕ) [NeZero M]
    (i : Fin (M^d*(f.length*2))) : Fin (n*2*M^d) × Fin (n*2*M^d) :=
  let row : Fin (M^d) := ⟨i.val/(f.length*2),Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using i.isLt)⟩
  let position : Fin (f.length*2) := ⟨i.val%(f.length*2),Nat.mod_lt _ (by
    have hi := i.isLt
    have nonzero : f.length≠0 := by intro zero; simp [zero] at hi
    omega)⟩
  let arc := paddedArcAt positive f[position.val/2] ⟨position.val%2,by omega⟩
  (coverIndex n d M (arc.source,(coordinateIndex d M).symm row),
    coverIndex n d M (arc.target,(coordinateIndex d M).symm row+wrap M arc.offset))

theorem paddedCoverEdges_ofFn (positive : 0<n) (f : Formula (Fin n) d) :
    paddedCoverEdges positive f M=List.ofFn (paddedEdgeAt positive f M) := by
  rw [paddedCoverEdges,paddedArcs_ofFn]
  simp only [List.map_ofFn]
  rw [flatMap_as_flatten,← List.ofFn_eq_map,TwoSATBatch.flatten_ofFn_blocks]
  rfl

theorem paddedCoverEdges_lookup (positive : 0<n) (f : Formula (Fin n) d)
    (i : Fin (M^d*(f.length*2))) :
    (paddedCoverEdges positive f M)[i.val]?=some (paddedEdgeAt positive f M i) := by
  rw [paddedCoverEdges_ofFn]
  simp

end LeanTrominoes.PeriodicTwoSAT.WordRAM
