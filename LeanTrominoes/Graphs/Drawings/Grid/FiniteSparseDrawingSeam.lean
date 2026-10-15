/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Tromino.Finite.FiniteSparseAssignmentSeamCompiler
import LeanTrominoes.Graphs.Drawings.Orthogonal.OrthogonalDrawingMoveSeam
import LeanTrominoes.Tiling.Tromino.Gadgets.GadgetSparseExpandedMotif

/-! # Sparse readback after moving the finite drawing seam -/
namespace LeanTrominoes.FiniteSparseAssignmentSeamCompiler
open Gadget Gadget.PeriodicOrthogonalDrawing

theorem lookup_shift (assignments : List (Cell × OrthogonalCellType)) (location : Cell) :
    (assignments.map shift).lookup location=
      assignments.lookup (location.1+1,location.2+1) := by
  rcases location with ⟨x,y⟩
  induction assignments with
  | nil => rfl
  | cons assignment assignments ih =>
      rcases assignment with ⟨⟨a,b⟩,cell⟩
      simp only [List.map_cons,shift,List.lookup_cons]
      have equal : (((x,y):Cell)==(a-1,b-1))=
          (((x+1,y+1):Cell)==(a,b)) := by
        apply Bool.eq_iff_iff.mpr
        simp only [beq_iff_eq,Prod.mk.injEq]
        omega
      rw [equal,ih]

theorem keysNodup_shift (assignments : List (Cell × OrthogonalCellType))
    (nodup : (assignments.map Prod.fst).Nodup) :
    ((assignments.map shift).map Prod.fst).Nodup := by
  have inj : Function.Injective (fun point : Cell => (point.1-1,point.2-1)) := by
    intro first second equal
    apply Prod.ext
    · have eq := congrArg Prod.fst equal
      change first.1-1=second.1-1 at eq
      omega
    · have eq := congrArg Prod.snd equal
      change first.2-1=second.2-1 at eq
      omega
  simpa only [List.map_map,Function.comp_def,shift] using nodup.map inj

/-- The original first row and column are blank, so subtraction creates no
wrapped records at the last row or column. -/
theorem moveSeam_lookup (drawing : PeriodicOrthogonalDrawing)
    (assignments : List (Cell × OrthogonalCellType))
    (bounds : ∀ assignment∈assignments,
      0<assignment.1.1 ∧ assignment.1.1<(drawing.horizontalPeriod:Int) ∧
      0<assignment.1.2 ∧ assignment.1.2<(drawing.verticalPeriod:Int))
    (readback : ∀ position : drawing.Position,
      drawing.get position=(assignments.lookup (((position.1.val:Int),(position.2.val:Int)):Cell)).getD .blank)
    (firstColumn : ∀ y,drawing.get (0,y)=.blank)
    (firstRow : ∀ x,drawing.get (x,0)=.blank) (position : drawing.Position) :
    drawing.moveSeam.get position=
      ((assignments.map shift).lookup (((position.1.val:Int),(position.2.val:Int)):Cell)).getD .blank := by
  rw [lookup_shift]
  by_cases horizontal : position.1.val+1<drawing.horizontalPeriod
  · by_cases vertical : position.2.val+1<drawing.verticalPeriod
    · rw [moveSeam_get,readback]
      have xEq : (drawing.seamPosition position).1.val=position.1.val+1 := by
        simpa [seamPosition,Fin.val_add,Nat.add_mod,horizontalPeriod,verticalPeriod] using Nat.mod_eq_of_lt horizontal
      have yEq : (drawing.seamPosition position).2.val=position.2.val+1 := by
        simpa [seamPosition,Fin.val_add,Nat.add_mod,horizontalPeriod,verticalPeriod] using Nat.mod_eq_of_lt vertical
      rw [xEq,yEq]
      push_cast
      rfl
    · have last : position.2.val+1=drawing.verticalPeriod := by
        have lt := position.2.isLt
        change position.2.val<drawing.verticalPeriod at lt
        omega
      rw [drawing.moveSeam_blankBoundary firstColumn firstRow position (Or.inr last)]
      have none : assignments.lookup ((position.1.val:Int)+1,(position.2.val:Int)+1)=none := by
        rw [List.lookup_eq_none_iff]
        intro assignment member
        rw [bne_iff_ne]
        intro eq
        have yEq := congrArg Prod.snd eq
        have inside := bounds assignment member
        omega
      rw [none]
      rfl
  · have last : position.1.val+1=drawing.horizontalPeriod := by
      have lt := position.1.isLt
      change position.1.val<drawing.horizontalPeriod at lt
      omega
    rw [drawing.moveSeam_blankBoundary firstColumn firstRow position (Or.inl last)]
    have none : assignments.lookup ((position.1.val:Int)+1,(position.2.val:Int)+1)=none := by
      rw [List.lookup_eq_none_iff]
      intro assignment member
      rw [bne_iff_ne]
      intro eq
      have xEq := congrArg Prod.fst eq
      have inside := bounds assignment member
      omega
    rw [none]
    rfl

/-- The sparse finite output has exactly the cells of the complete shifted
raster, with no enumeration of its blank area. -/
theorem mem_shiftedMotif_iff (drawing : PeriodicOrthogonalDrawing)
    (assignments : List (Cell × OrthogonalCellType))
    (nodup : (assignments.map Prod.fst).Nodup)
    (bounds : ∀ assignment∈assignments,
      0<assignment.1.1 ∧ assignment.1.1<(drawing.horizontalPeriod:Int) ∧
      0<assignment.1.2 ∧ assignment.1.2<(drawing.verticalPeriod:Int))
    (readback : ∀ position : drawing.Position,
      drawing.get position=(assignments.lookup (((position.1.val:Int),(position.2.val:Int)):Cell)).getD .blank)
    (firstColumn : ∀ y,drawing.get (0,y)=.blank)
    (firstRow : ∀ x,drawing.get (x,0)=.blank) (t : Tromino) (cell : Cell) :
    cell∈sparseExpandedMotif t (assignments.map shift) ↔
      cell∈drawing.moveSeam.expandedMotif t := by
  rw [← drawing.moveSeam.computableExpandedMotif_eq t]
  apply mem_sparseExpandedMotif_iff t drawing.moveSeam (assignments.map shift)
    (keysNodup_shift assignments nodup)
  · intro assignment member
    obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
    have inside := bounds original originalMember
    change 0≤original.1.1-1 ∧ original.1.1-1<(drawing.horizontalPeriod:Int) ∧
      0≤original.1.2-1 ∧ original.1.2-1<(drawing.verticalPeriod:Int)
    omega
  · intro x y hx hy
    exact moveSeam_lookup drawing assignments bounds readback firstColumn firstRow
      (⟨x,hx⟩,⟨y,hy⟩)
end LeanTrominoes.FiniteSparseAssignmentSeamCompiler
