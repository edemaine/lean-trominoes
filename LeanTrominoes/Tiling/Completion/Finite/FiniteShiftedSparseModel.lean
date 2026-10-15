/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Completion.CompletionSparseDrawing
import LeanTrominoes.Graphs.Drawings.Grid.FiniteSparseDrawingSeam

/-! # Sparse completion queries after moving the finite seam -/
namespace LeanTrominoes.CompletionPattern.Runtime
open Gadget Gadget.PeriodicOrthogonalDrawing FiniteSparseAssignmentSeamCompiler

private theorem position_nat_eq (d : PeriodicOrthogonalDrawing) (c : Cell)
    (hc : 0≤c.1 ∧ c.1<d.horizontalPeriod ∧ 0≤c.2 ∧ c.2<d.verticalPeriod) :
    (((d.positionAt c).1.val:Int),((d.positionAt c).2.val:Int))=c := by
  have hx := Int.emod_eq_of_lt hc.1 hc.2.1
  have hy := Int.emod_eq_of_lt hc.2.2.1 hc.2.2.2
  apply Prod.ext <;> simp only [positionAt,residue]
  · change ((c.1%(d.horizontalPeriod:Int)).toNat:Int)=c.1
    rw [hx,Int.toNat_of_nonneg hc.1]
  · change ((c.2%(d.verticalPeriod:Int)).toNat:Int)=c.2
    rw [hy,Int.toNat_of_nonneg hc.2.2.1]

theorem shiftedSparseModel (drawing : PeriodicOrthogonalDrawing) (entries : List DrawingEntry)
    (nodup : (entries.map Prod.fst).Nodup)
    (bounds : ∀ a∈entries,0<a.1.1 ∧ a.1.1<drawing.horizontalPeriod ∧
      0<a.1.2 ∧ a.1.2<drawing.verticalPeriod)
    (readback : ∀ position : drawing.Position,drawing.get position=
      (entries.lookup (((position.1.val:Int),(position.2.val:Int)):Cell)).getD .blank)
    (firstColumn : ∀ y,drawing.get (0,y)=.blank)
    (firstRow : ∀ x,drawing.get (x,0)=.blank) :
    SparseModel drawing.moveSeam (entries.map shift) := by
  have shiftedBounds (a : DrawingEntry) (ha : a∈entries.map shift) :
      0≤a.1.1 ∧ a.1.1<drawing.moveSeam.horizontalPeriod ∧
      0≤a.1.2 ∧ a.1.2<drawing.moveSeam.verticalPeriod := by
    obtain ⟨original,member,rfl⟩ := List.mem_map.mp ha
    have inside := bounds original member
    change 0≤original.1.1-1 ∧ original.1.1-1<drawing.horizontalPeriod ∧
      0≤original.1.2-1 ∧ original.1.2-1<drawing.verticalPeriod
    omega
  have lookup (c : Cell) (hc : 0≤c.1 ∧ c.1<drawing.moveSeam.horizontalPeriod ∧
      0≤c.2 ∧ c.2<drawing.moveSeam.verticalPeriod) :
      drawing.moveSeam.getAt c=((entries.map shift).lookup c).getD .blank := by
    unfold getAt
    rw [moveSeam_lookup drawing entries bounds readback firstColumn firstRow,
      position_nat_eq drawing.moveSeam c hc]
  refine ⟨shiftedBounds,?_,lookup⟩
  intro a member
  rw [lookup a.1 (shiftedBounds a member),
    PeriodicThreeDM.List.lookup_eq_some_of_mem_of_nodup_keys member (keysNodup_shift entries nodup)]
  rfl
end LeanTrominoes.CompletionPattern.Runtime
