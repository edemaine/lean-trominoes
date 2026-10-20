/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMGlobalInitialize
import LeanTrominoes.Tiling.Domino.DominoWordRAMGlobalPrepareBounds
import LeanTrominoes.Tiling.Domino.DominoWordRAMSizeBounds

/-! # One global arena and its physical endpoint-array bounds -/
namespace LeanTrominoes.Domino.WordRAM.Driver
open ComplexityAbstract.RAM Binary
variable {n d : ℕ}

 theorem inputEnd_eq (B : BasisData n d) : GlobalPrepare128.inputEnd B=Candidate.inputEnd B := by
  unfold GlobalPrepare128.inputEnd Candidate.inputEnd
  rw [words_eq_map,List.length_map]

 theorem endAddress_eq (B : BasisData n d) : GlobalPrepare128.endAddress B=
    Candidate.inputEnd B+SizeBounds.initialFactor d*precision B := by
  unfold GlobalPrepare128.endAddress GlobalPrepare128.factor SizeBounds.initialFactor
  rw [inputEnd_eq]

 theorem edgeCount_eq (n d : ℕ) : edgeCount n d=SizeBounds.edgeCount n d := by
  unfold edgeCount SizeBounds.edgeCount
  ring

 theorem driverHeap_eq (B : BasisData n d) : SizeBounds.driverHeap B=
    GlobalPrepare128.endAddress B+2*edgeCount n d+n*n*SizeBounds.uniformSpace d*precision B := by
  rw [endAddress_eq,edgeCount_eq]
  rfl

 theorem heap_le_operation (B : BasisData n d) : SizeBounds.driverHeap B≤SizeBounds.operationBound B := by
  have scalar : SizeBounds.driverHeap B≤FreshProbe.scalarBound (Candidate.slotBound d) (SizeBounds.driverHeap B) := by
    unfold FreshProbe.scalarBound
    nlinarith
  unfold SizeBounds.operationBound
  omega

 theorem initial_tables_bound (B : BasisData n d) : GlobalPrepare128.endAddress B+2*edgeCount n d≤SizeBounds.driverHeap B := by
  rw [driverHeap_eq]
  omega

 theorem initial_base_four (B : BasisData n d) : 4≤GlobalPrepare128.endAddress B := by
  rw [endAddress_eq]
  have four := Candidate.inputEnd_four B
  omega

 theorem graphResources (B : BasisData n d) : GraphResources (SizeBounds.operationBound B) n d
    (GlobalPrepare128.endAddress B) (edgeCount n d) := by
  have heap := heap_le_operation B
  have tables := (initial_tables_bound B).trans heap
  have positive : 0<n+1 := by omega
  have power : 2^d≤(n+1)*2^d := Nat.le_mul_of_pos_left _ positive
  have vertices : n*2^d≤(n+1)*2^d := Nat.mul_le_mul_right _ (by omega)
  refine ⟨?_,?_,?_,?_,tables,?_⟩
  · unfold SizeBounds.operationBound; omega
  · unfold SizeBounds.operationBound; omega
  · unfold SizeBounds.operationBound; omega
  · unfold SizeBounds.operationBound; omega
  · omega

end LeanTrominoes.Domino.WordRAM.Driver
