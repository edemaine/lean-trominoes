/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingInteriorBends
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRealLocalBounds

/-! # Strict interior representatives and local cell labels for moved bends -/
namespace LeanTrominoes.PeriodicGridDrawing.InteriorBends

def cell (grid factor : Int) (p : Cell) : Cell :=
  ((coordinate grid factor p.1)/(factor*grid),(coordinate grid factor p.2)/(factor*grid))
def representative (grid factor : Int) (p : Cell) : Cell :=
  ((coordinate grid factor p.1)%(factor*grid),(coordinate grid factor p.2)%(factor*grid))

theorem point_decomposition (grid factor : Int) (p : Cell) :
    point grid factor p=Cell.add (representative grid factor p) (Cell.scale (factor*grid) (cell grid factor p)) := by
  apply Prod.ext <;> simp only [point,representative,cell,Cell.add,Cell.scale]
  · exact (Int.emod_add_mul_ediv _ _).symm
  · exact (Int.emod_add_mul_ediv _ _).symm

theorem representative_interior {grid factor : Int} (gridPositive : 0<grid) (spacing : 2<factor) (p : Cell) :
    0<(representative grid factor p).1 ∧ (representative grid factor p).1<factor*grid ∧
    0<(representative grid factor p).2 ∧ (representative grid factor p).2<factor*grid := by
  have periodPositive : 0<factor*grid := mul_pos (by omega) gridPositive
  have coordinateBounds (value : Int) :
      0<coordinate grid factor value%(factor*grid) ∧ coordinate grid factor value%(factor*grid)<factor*grid := by
    have nonnegative := Int.emod_nonneg (coordinate grid factor value) periodPositive.ne'
    have nonzero := coordinate_off_seams gridPositive spacing (value := value)
    exact ⟨by omega,Int.emod_lt_of_pos _ periodPositive⟩
  exact ⟨(coordinateBounds p.1).1,(coordinateBounds p.1).2,(coordinateBounds p.2).1,(coordinateBounds p.2).2⟩

theorem zero_cell_coordinate {grid factor value : Int} (gridPositive : 0<grid) (spacing : 2<factor)
    (bounds : 0≤value ∧ value≤grid) : coordinate grid factor value/(factor*grid)=0 := by
  have h := coordinate_in_zero_cell gridPositive spacing bounds
  exact Int.ediv_eq_zero_of_lt h.1.le h.2

theorem east_cell_coordinate {grid factor value : Int} (gridPositive : 0<grid) (spacing : 2<factor)
    (bounds : 0≤value ∧ value≤2*grid) :
    coordinate grid factor value/(factor*grid)=0 ∨ coordinate grid factor value/(factor*grid)=1 := by
  have h := coordinate_in_east_cells gridPositive spacing bounds
  have periodPositive : 0<factor*grid := mul_pos (by omega) gridPositive
  have lo := Int.ediv_nonneg h.1.le periodPositive.le
  have hi := Int.ediv_lt_of_lt_mul periodPositive h.2
  omega

theorem west_cell_coordinate {grid factor value : Int} (gridPositive : 0<grid) (spacing : 2<factor)
    (bounds : -grid≤value ∧ value≤grid) :
    coordinate grid factor value/(factor*grid)= -1 ∨ coordinate grid factor value/(factor*grid)=0 := by
  have h := coordinate_in_west_cells gridPositive spacing bounds
  have periodPositive : 0<factor*grid := mul_pos (by omega) gridPositive
  have lo := Int.le_ediv_of_mul_le periodPositive (show (-1)*(factor*grid)≤coordinate grid factor value by nlinarith [h.1])
  have hi := Int.ediv_lt_of_lt_mul periodPositive (show coordinate grid factor value<1*(factor*grid) by simpa using h.2)
  omega

theorem cell_interior {grid factor : Int} (gridPositive : 0<grid) (spacing : 2<factor) {p : Cell}
    (bounds : 0<p.1 ∧ p.1<grid ∧ 0<p.2 ∧ p.2<grid) : cell grid factor p=(0,0) := by
  simp only [cell,zero_cell_coordinate gridPositive spacing ⟨bounds.1.le,bounds.2.1.le⟩,
    zero_cell_coordinate gridPositive spacing ⟨bounds.2.2.1.le,bounds.2.2.2.le⟩]

theorem representative_of_interior {grid factor : Int} (gridPositive : 0<grid) (spacing : 2<factor) {p : Cell}
    (bounds : 0<p.1 ∧ p.1<grid ∧ 0<p.2 ∧ p.2<grid) : representative grid factor p=Cell.scale factor p := by
  have decomposition := point_decomposition grid factor p
  rw [cell_interior gridPositive spacing bounds] at decomposition
  simpa only [Cell.scale,Cell.add,mul_zero,add_zero,point_interior bounds] using decomposition.symm

theorem cells_allowed {drawing : PeriodicGridDrawing} {factor : Int} (spacing : 2<factor) {offset p : Cell}
    (localOffset : offset.1.natAbs+offset.2.natAbs≤1)
    (bounds : drawing.PointInLocalRectangle offset p) :
    cell drawing.gridSize factor p=(0,0) ∨ cell drawing.gridSize factor p=offset := by
  have positive : (0:Int)<drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have offsets := PeriodicOrthocrossing.offset_eq_of_span_le_one (⟨(),(),offset⟩ : PeriodicEdge Unit) localOffset
  rcases offsets with rfl | rfl | rfl | rfl | rfl
  · simp only [PointInLocalRectangle,mul_zero,min_self,max_self,add_zero] at bounds
    left
    simp only [cell,zero_cell_coordinate positive spacing ⟨bounds.1,bounds.2.1⟩,
      zero_cell_coordinate positive spacing ⟨bounds.2.2.1,bounds.2.2.2⟩]
  · simp [PointInLocalRectangle,positive.le] at bounds
    have x := east_cell_coordinate positive spacing (bounds := ⟨bounds.1,by simpa [two_mul] using bounds.2.1⟩)
    have y := zero_cell_coordinate positive spacing ⟨bounds.2.2.1,bounds.2.2.2⟩
    rcases x with x | x
    · left; simp [cell,x,y]
    · right; simp [cell,x,y]
  · simp [PointInLocalRectangle,positive.le] at bounds
    have x := west_cell_coordinate positive spacing (bounds := ⟨bounds.1,bounds.2.1⟩)
    have y := zero_cell_coordinate positive spacing ⟨bounds.2.2.1,bounds.2.2.2⟩
    rcases x with x | x
    · right; simp [cell,x,y]
    · left; simp [cell,x,y]
  · simp [PointInLocalRectangle,positive.le] at bounds
    have x := zero_cell_coordinate positive spacing ⟨bounds.1,bounds.2.1⟩
    have y := east_cell_coordinate positive spacing (bounds := ⟨bounds.2.2.1,by simpa [two_mul] using bounds.2.2.2⟩)
    rcases y with y | y
    · left; simp [cell,x,y]
    · right; simp [cell,x,y]
  · simp [PointInLocalRectangle,positive.le] at bounds
    have x := zero_cell_coordinate positive spacing ⟨bounds.1,bounds.2.1⟩
    have y := west_cell_coordinate positive spacing (bounds := ⟨bounds.2.2.1,bounds.2.2.2⟩)
    rcases y with y | y
    · right; simp [cell,x,y]
    · left; simp [cell,x,y]

end LeanTrominoes.PeriodicGridDrawing.InteriorBends
