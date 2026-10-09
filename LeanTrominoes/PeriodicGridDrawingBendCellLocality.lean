/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingBendCells

/-! # Bend subdivision preserves local offsets and original vertex positions -/
namespace LeanTrominoes.PeriodicGridDrawing.InteriorBends

theorem cell_difference_span {first second offset : Cell}
    (firstCell : first=(0,0) ∨ first=offset) (secondCell : second=(0,0) ∨ second=offset)
    (localOffset : offset.1.natAbs+offset.2.natAbs≤1) :
    (Cell.sub second first).1.natAbs+(Cell.sub second first).2.natAbs≤1 := by
  rcases firstCell with rfl | rfl <;> rcases secondCell with rfl | rfl <;>
    simp_all [Cell.sub]

theorem subsegment_cell_locality {drawing : PeriodicGridDrawing} {factor : Int} (spacing : 2<factor)
    {offset first second : Cell} (localOffset : offset.1.natAbs+offset.2.natAbs≤1)
    (firstBounds : drawing.PointInLocalRectangle offset first)
    (secondBounds : drawing.PointInLocalRectangle offset second) :
    (Cell.sub (cell drawing.gridSize factor second) (cell drawing.gridSize factor first)).1.natAbs+
      (Cell.sub (cell drawing.gridSize factor second) (cell drawing.gridSize factor first)).2.natAbs≤1 :=
  cell_difference_span (cells_allowed spacing localOffset firstBounds) (cells_allowed spacing localOffset secondBounds) localOffset

theorem coordinate_translated_interior {grid factor value : Int} (lo : 0<value) (hi : value<grid) (translate : Int) :
    coordinate grid factor (value+grid*translate)=factor*value+(factor*grid)*translate := by
  have remainder : (value+grid*translate)%grid=value := by
    rw [Int.add_mul_emod_self_left,Int.emod_eq_of_lt lo.le hi]
  simp only [coordinate,correction,remainder,if_neg (show value≠0 by omega),add_zero]
  ring

private theorem quotient_translated {grid factor value : Int} (gridPositive : 0<grid) (spacing : 2<factor)
    (lo : 0<value) (hi : value<grid) (translate : Int) :
    coordinate grid factor (value+grid*translate)/(factor*grid)=translate := by
  have periodPositive : 0<factor*grid := mul_pos (by omega) gridPositive
  have scalarBounds : 0≤factor*value ∧ factor*value<factor*grid := by constructor <;> nlinarith
  rw [coordinate_translated_interior lo hi]
  have reordered : factor*value+(factor*grid)*translate=translate*(factor*grid)+factor*value := by ring
  rw [reordered,Int.mul_add_ediv_right _ _ periodPositive.ne',Int.ediv_eq_zero_of_lt scalarBounds.1 scalarBounds.2,add_zero]

private theorem remainder_translated {grid factor value : Int} (spacing : 2<factor)
    (lo : 0<value) (hi : value<grid) (translate : Int) :
    coordinate grid factor (value+grid*translate)%(factor*grid)=factor*value := by
  have scalarBounds : 0≤factor*value ∧ factor*value<factor*grid := by constructor <;> nlinarith
  rw [coordinate_translated_interior lo hi,Int.add_mul_emod_self_left,
    Int.emod_eq_of_lt scalarBounds.1 scalarBounds.2]

theorem cell_translated_interior {grid factor : Int} (gridPositive : 0<grid) (spacing : 2<factor)
    {p : Cell} (bounds : 0<p.1 ∧ p.1<grid ∧ 0<p.2 ∧ p.2<grid) (translate : Cell) :
    cell grid factor (Cell.add p (Cell.scale grid translate))=translate := by
  apply Prod.ext
  · exact quotient_translated gridPositive spacing bounds.1 bounds.2.1 translate.1
  · exact quotient_translated gridPositive spacing bounds.2.2.1 bounds.2.2.2 translate.2

theorem representative_translated_interior {grid factor : Int} (spacing : 2<factor)
    {p : Cell} (bounds : 0<p.1 ∧ p.1<grid ∧ 0<p.2 ∧ p.2<grid) (translate : Cell) :
    representative grid factor (Cell.add p (Cell.scale grid translate))=Cell.scale factor p := by
  apply Prod.ext
  · exact remainder_translated spacing bounds.1 bounds.2.1 translate.1
  · exact remainder_translated spacing bounds.2.2.1 bounds.2.2.2 translate.2

theorem point_translated_interior {grid factor : Int}
    {p : Cell} (bounds : 0<p.1 ∧ p.1<grid ∧ 0<p.2 ∧ p.2<grid) (translate : Cell) :
    point grid factor (Cell.add p (Cell.scale grid translate))=
      Cell.add (Cell.scale factor p) (Cell.scale (factor*grid) translate) := by
  apply Prod.ext
  · exact coordinate_translated_interior bounds.1 bounds.2.1 translate.1
  · exact coordinate_translated_interior bounds.2.2.1 bounds.2.2.2 translate.2

end LeanTrominoes.PeriodicGridDrawing.InteriorBends
