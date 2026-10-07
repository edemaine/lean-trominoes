/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.OrthogonalBoundaryCellSeparation

/-! # Rectangle routes in columns separated by crossing strips -/
namespace LeanTrominoes.OrthogonalBoundaryRouting
open PeriodicOrthocrossing

def slabOffset (pitch height inset : Int) (cell : Cell) : Cell := (pitch*cell.1+inset,height*cell.2)

theorem separated_closed_bands_disjoint {pitch width firstShift secondShift : Int}
    (positive : 0 < pitch) (gap : width < pitch) (different : firstShift ≠ secondShift) {point : ℝ}
    (firstBounds : 0 ≤ point-(pitch : ℝ)*firstShift ∧ point-(pitch : ℝ)*firstShift ≤ width)
    (secondBounds : 0 ≤ point-(pitch : ℝ)*secondShift ∧ point-(pitch : ℝ)*secondShift ≤ width) : False := by
  have realPositive : (0 : ℝ) < pitch := by exact_mod_cast positive
  have realGap : (width : ℝ) < pitch := by exact_mod_cast gap
  rcases lt_or_gt_of_ne different with before | after
  · have step : (firstShift : ℝ)+1 ≤ secondShift := by exact_mod_cast (by omega : firstShift+1 ≤ secondShift)
    have scaled := mul_le_mul_of_nonneg_left step realPositive.le
    nlinarith [firstBounds.2,secondBounds.1]
  · have step : (secondShift : ℝ)+1 ≤ firstShift := by exact_mod_cast (by omega : secondShift+1 ≤ firstShift)
    have scaled := mul_le_mul_of_nonneg_left step realPositive.le
    nlinarith [firstBounds.1,secondBounds.2]

theorem distinct_slabs_contact_first_endpoint {pitch inset width height firstDepth secondDepth margin : Int}
    {first last secondFirst secondLast : Port} {firstCell secondCell : Cell}
    (pitchPositive : 0 < pitch) (stripGap : width < pitch)
    (firstPositive : 0 < firstDepth) (secondPositive : 0 < secondDepth)
    (firstDepthBound : firstDepth ≤ margin) (secondDepthBound : secondDepth ≤ margin)
    (room : 2*margin < width ∧ 2*margin < height)
    (firstInside : first.Inside width height margin) (lastInside : last.Inside width height margin)
    (secondFirstInside : secondFirst.Inside width height margin) (secondLastInside : secondLast.Inside width height margin)
    (firstOrder : first.Before last) (different : firstCell ≠ secondCell) {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains
      (translatePolyline (slabOffset pitch height inset firstCell) (route width height firstDepth first last)) point)
    (secondContains : GridPolyline.RealContains
      (translatePolyline (slabOffset pitch height inset secondCell) (route width height secondDepth secondFirst secondLast)) point) :
    GridPolyline.RealIsEndpoint
      (translatePolyline (slabOffset pitch height inset firstCell) (route width height firstDepth first last)) point := by
  have firstLocal := (GridPolyline.realContains_translate_inverse _ _ _).mp firstContains
  have secondLocal := (GridPolyline.realContains_translate_inverse _ _ _).mp secondContains
  have firstBounds := route_real_bounds firstPositive firstDepthBound room firstInside lastInside firstLocal
  have secondBounds := route_real_bounds secondPositive secondDepthBound room secondFirstInside secondLastInside secondLocal
  have heightPositive : 0 < height := by omega
  have boundary : point.1-(slabOffset pitch height inset firstCell).1 = 0 ∨
      point.1-(slabOffset pitch height inset firstCell).1 = width ∨
      point.2-(slabOffset pitch height inset firstCell).2 = 0 ∨
      point.2-(slabOffset pitch height inset firstCell).2 = height := by
    simp only [slabOffset,Prod.fst,Prod.snd,Int.cast_add,Int.cast_mul] at firstBounds secondBounds ⊢
    by_cases sameX : firstCell.1 = secondCell.1
    · have differentY : firstCell.2 ≠ secondCell.2 := fun sameY => different (Prod.ext sameX sameY)
      have contact := closed_cell_band_contact_boundary heightPositive differentY firstBounds.2.2 secondBounds.2.2
      exact contact.elim (fun on => Or.inr (Or.inr (Or.inl on))) (fun on => Or.inr (Or.inr (Or.inr on)))
    · exact False.elim (separated_closed_bands_disjoint (point := point.1-inset) pitchPositive stripGap sameX
        ⟨by linarith [firstBounds.1],by linarith [firstBounds.2.1]⟩
        ⟨by linarith [secondBounds.1],by linarith [secondBounds.2.1]⟩)
  have portContact := route_boundary_contact_ports firstPositive firstDepthBound room firstInside lastInside firstOrder firstLocal boundary
  rcases portContact with atFirst | atLast
  · refine Or.inl ⟨Cell.add (slabOffset pitch height inset firstCell) (first.point width height),?_,real_point_translate_back atFirst⟩
    simp only [translatePolyline,List.head?_map,route_head,Option.map_some]
  · refine Or.inr ⟨Cell.add (slabOffset pitch height inset firstCell) (last.point width height),?_,real_point_translate_back atLast⟩
    simp only [translatePolyline,List.getLast?_map,route_last,Option.map_some]

end LeanTrominoes.OrthogonalBoundaryRouting
