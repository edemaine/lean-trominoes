/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.OrthogonalBoundaryArcBounds
import LeanTrominoes.Common.Geometry.GridPolylineRealPeriodicSeparation

/-! # Periodic rectangular cells meet only along their boundary ports -/
namespace LeanTrominoes.OrthogonalBoundaryRouting
open PeriodicOrthocrossing

def cellOffset (width height : Int) (cell : Cell) : Cell := (width*cell.1,height*cell.2)

theorem closed_cell_band_contact_boundary {period firstShift secondShift : Int}
    (positive : 0 < period) (different : firstShift ≠ secondShift) {point : ℝ}
    (firstBounds : 0 ≤ point-(period : ℝ)*firstShift ∧ point-(period : ℝ)*firstShift ≤ period)
    (secondBounds : 0 ≤ point-(period : ℝ)*secondShift ∧ point-(period : ℝ)*secondShift ≤ period) :
    point-(period : ℝ)*firstShift = 0 ∨ point-(period : ℝ)*firstShift = period := by
  have realPositive : (0 : ℝ) < period := by exact_mod_cast positive
  rcases lt_or_gt_of_ne different with before | after
  · have step : (firstShift : ℝ)+1 ≤ secondShift := by exact_mod_cast (by omega : firstShift+1 ≤ secondShift)
    have scaled := mul_le_mul_of_nonneg_left step realPositive.le
    exact Or.inr (by nlinarith [firstBounds.2,secondBounds.1])
  · have step : (secondShift : ℝ)+1 ≤ firstShift := by exact_mod_cast (by omega : secondShift+1 ≤ firstShift)
    have scaled := mul_le_mul_of_nonneg_left step realPositive.le
    exact Or.inl (by nlinarith [firstBounds.1,secondBounds.2])

theorem real_point_translate_back {offset endpoint : Cell} {point : ℝ × ℝ}
    (equal : (point.1-offset.1,point.2-offset.2) = realCell endpoint) :
    point = realCell (Cell.add offset endpoint) := by
  have x := congrArg Prod.fst equal
  have y := congrArg Prod.snd equal
  simp only [realCell,Prod.fst,Prod.snd] at x y
  apply Prod.ext <;> simp only [realCell,Cell.add,Prod.fst,Prod.snd,Int.cast_add] <;> linarith

theorem distinct_cells_contact_first_endpoint {width height firstDepth secondDepth margin : Int}
    {first last secondFirst secondLast : Port} {firstCell secondCell : Cell}
    (firstPositive : 0 < firstDepth) (secondPositive : 0 < secondDepth)
    (firstDepthBound : firstDepth ≤ margin) (secondDepthBound : secondDepth ≤ margin)
    (room : 2*margin < width ∧ 2*margin < height)
    (firstInside : first.Inside width height margin) (lastInside : last.Inside width height margin)
    (secondFirstInside : secondFirst.Inside width height margin) (secondLastInside : secondLast.Inside width height margin)
    (firstOrder : first.Before last) (different : firstCell ≠ secondCell) {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains
      (translatePolyline (cellOffset width height firstCell) (route width height firstDepth first last)) point)
    (secondContains : GridPolyline.RealContains
      (translatePolyline (cellOffset width height secondCell) (route width height secondDepth secondFirst secondLast)) point) :
    GridPolyline.RealIsEndpoint
      (translatePolyline (cellOffset width height firstCell) (route width height firstDepth first last)) point := by
  have firstLocal := (GridPolyline.realContains_translate_inverse _ _ _).mp firstContains
  have secondLocal := (GridPolyline.realContains_translate_inverse _ _ _).mp secondContains
  have firstBounds := route_real_bounds firstPositive firstDepthBound room firstInside lastInside firstLocal
  have secondBounds := route_real_bounds secondPositive secondDepthBound room secondFirstInside secondLastInside secondLocal
  have widthPositive : 0 < width := by omega
  have heightPositive : 0 < height := by omega
  have boundary : (point.1-(cellOffset width height firstCell).1) = 0 ∨
      (point.1-(cellOffset width height firstCell).1) = width ∨
      (point.2-(cellOffset width height firstCell).2) = 0 ∨
      (point.2-(cellOffset width height firstCell).2) = height := by
    simp only [cellOffset,Prod.fst,Prod.snd,Int.cast_mul] at firstBounds secondBounds ⊢
    by_cases sameX : firstCell.1 = secondCell.1
    · have differentY : firstCell.2 ≠ secondCell.2 := fun sameY => different (Prod.ext sameX sameY)
      have contact := closed_cell_band_contact_boundary heightPositive differentY firstBounds.2.2 secondBounds.2.2
      exact contact.elim (fun on => Or.inr (Or.inr (Or.inl on))) (fun on => Or.inr (Or.inr (Or.inr on)))
    · have contact := closed_cell_band_contact_boundary widthPositive sameX
        ⟨firstBounds.1,firstBounds.2.1⟩ ⟨secondBounds.1,secondBounds.2.1⟩
      exact contact.elim Or.inl (fun on => Or.inr (Or.inl on))
  have portContact := route_boundary_contact_ports firstPositive firstDepthBound room firstInside lastInside firstOrder firstLocal boundary
  rcases portContact with atFirst | atLast
  · refine Or.inl ⟨Cell.add (cellOffset width height firstCell) (first.point width height),?_,real_point_translate_back atFirst⟩
    simp only [translatePolyline,List.head?_map,route_head,Option.map_some]
  · refine Or.inr ⟨Cell.add (cellOffset width height firstCell) (last.point width height),?_,real_point_translate_back atLast⟩
    simp only [translatePolyline,List.getLast?_map,route_last,Option.map_some]

end LeanTrominoes.OrthogonalBoundaryRouting
