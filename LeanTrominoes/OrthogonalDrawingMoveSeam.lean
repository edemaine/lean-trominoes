/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteGadgetSubstitution
import LeanTrominoes.PeriodicThreeDMNormalizationRasterizationCorrectness

/-! # Move blank first rows and columns to the final boundary -/
namespace LeanTrominoes.Gadget.PeriodicOrthogonalDrawing
open PeriodicThreeDM

def moveSeam (drawing : PeriodicOrthogonalDrawing) : PeriodicOrthogonalDrawing where
  horizontalPeriodPred := drawing.horizontalPeriodPred
  verticalPeriodPred := drawing.verticalPeriodPred
  cellTypes := rowMajorList (drawing.verticalPeriodPred+1) (drawing.horizontalPeriodPred+1)
    (fun x y => drawing.getAt ((x:Int)+1,(y:Int)+1))

def seamPosition (drawing : PeriodicOrthogonalDrawing) (position : drawing.Position) : drawing.Position :=
  (position.1+1,position.2+1)

theorem moveSeam_get (drawing : PeriodicOrthogonalDrawing) (position : drawing.Position) :
    drawing.moveSeam.get position=drawing.get (drawing.seamPosition position) := by
  change (rowMajorList (drawing.verticalPeriodPred+1) (drawing.horizontalPeriodPred+1)
    (fun x y => drawing.getAt ((x:Int)+1,(y:Int)+1))).getD
      (position.2.val*(drawing.horizontalPeriodPred+1)+position.1.val) OrthogonalCellType.blank=_
  rw [rowMajorList_getD _ _ _ _ position.1.isLt position.2.isLt]
  have canonical : drawing.positionAt (position.1.val,position.2.val)=position := by
    simpa using drawing.positionAt_add_periods position 0 0
  simp only [getAt,positionAt,residue_add_one,seamPosition]
  exact congrArg drawing.get (congrArg (fun p : drawing.Position => (p.1+1,p.2+1)) canonical)

theorem seamPosition_neighbor (drawing : PeriodicOrthogonalDrawing) (position : drawing.Position) (side : Side) :
    drawing.seamPosition (drawing.neighbor position side)=drawing.neighbor (drawing.seamPosition position) side := by
  cases side <;> apply Prod.ext <;> simp [seamPosition,neighbor,sub_eq_add_neg,add_assoc,add_comm,add_left_comm]

theorem moveSeam_getAt (drawing : PeriodicOrthogonalDrawing) (location : Cell) :
    drawing.moveSeam.getAt location=drawing.getAt (location.1+1,location.2+1) := by
  rw [getAt,moveSeam_get]
  simp only [seamPosition,positionAt,moveSeam,getAt,residue_add_one]

private theorem shifted_neighbor (location : Cell) (side : Side) :
    ((latticeNeighbor location side).1+1,(latticeNeighbor location side).2+1)=
      latticeNeighbor (location.1+1,location.2+1) side := by
  cases side <;> simp [latticeNeighbor]

private theorem unshifted_neighbor (location : Cell) (side : Side) :
    ((latticeNeighbor location side).1-1,(latticeNeighbor location side).2-1)=
      latticeNeighbor (location.1-1,location.2-1) side := by
  cases side <;> simp [latticeNeighbor]

theorem moveSeam_isWellFormed (drawing : PeriodicOrthogonalDrawing) (wellFormed : drawing.IsWellFormed) :
    drawing.moveSeam.IsWellFormed := by
  constructor
  · simp [moveSeam,rowMajorList,List.length_flatMap,Nat.mul_comm]
  · intro position side
    change drawing.Position at position
    rw [moveSeam_get,moveSeam_get]
    change (drawing.get (drawing.seamPosition position)).portColor side=
      (drawing.get (drawing.seamPosition (drawing.neighbor position side))).portColor side.opposite
    rw [seamPosition_neighbor]
    exact wellFormed.2 _ side

theorem moveSeam_verticesSeparated (drawing : PeriodicOrthogonalDrawing) (separated : drawing.VerticesSeparated) :
    drawing.moveSeam.VerticesSeparated := by
  intro position side vertex
  change drawing.Position at position
  rw [moveSeam_get] at vertex
  rw [moveSeam_get]
  change (drawing.get (drawing.seamPosition (drawing.neighbor position side))).isVertex=false
  rw [seamPosition_neighbor]
  exact separated _ side vertex

theorem moveSeam_hasOrientation_iff (drawing : PeriodicOrthogonalDrawing) (wellFormed : drawing.IsWellFormed) :
    drawing.moveSeam.HasOrientation ↔ drawing.HasOrientation := by
  constructor
  · rintro ⟨_,orientation,valid⟩
    refine ⟨wellFormed,fun location side => orientation (location.1-1,location.2-1) side,?_,?_⟩
    · intro location
      have holds := valid.1 (location.1-1,location.2-1)
      rw [moveSeam_getAt] at holds
      simpa using holds
    · intro location side port
      have port' : ((drawing.moveSeam.getAt (location.1-1,location.2-1)).portColor side).isSome := by
        rw [moveSeam_getAt];simpa using port
      have holds := valid.2 (location.1-1,location.2-1) side port'
      simpa only [unshifted_neighbor] using holds
  · rintro ⟨_,orientation,valid⟩
    refine ⟨moveSeam_isWellFormed drawing wellFormed,
      fun location side => orientation (location.1+1,location.2+1) side,?_,?_⟩
    · intro location
      rw [moveSeam_getAt]
      exact valid.1 _
    · intro location side port
      rw [moveSeam_getAt] at port
      have holds := valid.2 (location.1+1,location.2+1) side port
      simpa only [shifted_neighbor] using holds

theorem moveSeam_blankBoundary (drawing : PeriodicOrthogonalDrawing)
    (firstColumn : ∀ y,drawing.get (0,y)=.blank)
    (firstRow : ∀ x,drawing.get (x,0)=.blank) : drawing.moveSeam.BlankBoundary := by
  intro position boundary
  change drawing.Position at position
  change position.1.val+1=drawing.horizontalPeriod ∨ position.2.val+1=drawing.verticalPeriod at boundary
  rw [moveSeam_get]
  rcases boundary with xLast|yLast
  · have xZero : position.1+1=0 := by
      apply Fin.ext
      have increment : (position.1+1).val=(position.1.val+1)%(drawing.horizontalPeriodPred+1) := by
        simp [Fin.val_add,Nat.add_mod]
      rw [increment,xLast]
      exact Nat.mod_self _
    simpa only [seamPosition,xZero] using firstColumn (position.2+1)
  · have yZero : position.2+1=0 := by
      apply Fin.ext
      have increment : (position.2+1).val=(position.2.val+1)%(drawing.verticalPeriodPred+1) := by
        simp [Fin.val_add,Nat.add_mod]
      rw [increment,yLast]
      exact Nat.mod_self _
    simpa only [seamPosition,yZero] using firstRow (position.1+1)
end LeanTrominoes.Gadget.PeriodicOrthogonalDrawing
