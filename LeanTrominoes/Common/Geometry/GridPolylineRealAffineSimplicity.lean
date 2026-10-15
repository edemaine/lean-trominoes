/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridPolylineRealOpenSimple
import LeanTrominoes.Common.Geometry.GridPolylineRealScaling
import LeanTrominoes.Common.Geometry.GridPolylineRealPeriodicSeparation
import LeanTrominoes.SAT.Planar.EmbeddedCNFIncidenceDrawingMapPoints

/-! # Real simplicity under injective affine coordinate changes -/
namespace LeanTrominoes.GridPolyline
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing PeriodicOrthocrossing

private theorem add_injective (offset : Cell) : Function.Injective (Cell.add offset) := by
  intro a b equal
  have hx := congrArg Prod.fst equal
  have hy := congrArg Prod.snd equal
  simp only [Cell.add] at hx hy
  exact Prod.ext (by omega) (by omega)

theorem IsRealSimple.map {route : List Cell} (simple : IsRealSimple route)
    (transform : Cell → Cell) (injective : Function.Injective transform) (inverse : (ℝ × ℝ) → (ℝ × ℝ))
    (segmentInverse : ∀ (segment : GridSegment) (point : ℝ × ℝ), (segment.mapPoints transform).RealContains point → segment.RealContains (inverse point))
    (endpointInverse : ∀ (point : ℝ × ℝ) (cell : Cell), inverse point = realCell cell → point = realCell (transform cell)) :
    IsRealSimple (route.map transform) := by
  refine ⟨by simpa using simple.1,?_,?_⟩
  · intro segment member
    rw [gridPolylineSegments_map_points] at member
    obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
    exact fun equal => simple.2.1 original originalMember (injective equal)
  · intro first firstMember second secondMember ordered point firstContains secondContains
    rw [gridPolylineSegments_map_points,List.zipIdx_map] at firstMember secondMember
    obtain ⟨a,am,rfl⟩ := List.mem_map.mp firstMember
    obtain ⟨b,bm,rfl⟩ := List.mem_map.mp secondMember
    have contact := simple.2.2 a am b bm ordered (inverse point)
      (segmentInverse a.1 point firstContains) (segmentInverse b.1 point secondContains)
    rcases contact with adjacent | closed
    · exact Or.inl ⟨adjacent.1,endpointInverse point a.1.finish adjacent.2⟩
    · refine Or.inr ⟨closed.1,?_,endpointInverse point a.1.start closed.2.2.1,
        endpointInverse point b.1.finish closed.2.2.2⟩
      simpa only [gridPolylineSegments_map_points,List.length_map,Prod.map,id_eq] using closed.2.1

theorem IsRealOpenSimple.map {route : List Cell} (simple : IsRealOpenSimple route)
    (transform : Cell → Cell) (injective : Function.Injective transform) (inverse : (ℝ × ℝ) → (ℝ × ℝ))
    (segmentInverse : ∀ (segment : GridSegment) (point : ℝ × ℝ), (segment.mapPoints transform).RealContains point → segment.RealContains (inverse point))
    (endpointInverse : ∀ (point : ℝ × ℝ) (cell : Cell), inverse point = realCell cell → point = realCell (transform cell)) :
    IsRealOpenSimple (route.map transform) := by
  refine ⟨by simpa using simple.1,?_,?_⟩
  · intro segment member
    rw [gridPolylineSegments_map_points] at member
    obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
    exact fun equal => simple.2.1 original originalMember (injective equal)
  · intro first firstMember second secondMember ordered point firstContains secondContains
    rw [gridPolylineSegments_map_points,List.zipIdx_map] at firstMember secondMember
    obtain ⟨a,am,rfl⟩ := List.mem_map.mp firstMember
    obtain ⟨b,bm,rfl⟩ := List.mem_map.mp secondMember
    have contact := simple.2.2 a am b bm ordered (inverse point)
      (segmentInverse a.1 point firstContains) (segmentInverse b.1 point secondContains)
    exact ⟨contact.1,endpointInverse point a.1.finish contact.2⟩

theorem IsRealSimple.translate {route : List Cell} (simple : IsRealSimple route) (offset : Cell) :
    IsRealSimple (translatePolyline offset route) := by
  apply simple.map (Cell.add offset) (add_injective offset)
    (fun point => (point.1-offset.1,point.2-offset.2))
  · intro segment point contains
    have shifted := GridSegment.realContains_translate segment offset (point.1-offset.1,point.2-offset.2)
    apply shifted.mp
    simpa [GridSegment.mapPoints,GridSegment.translate,Cell.add,add_comm] using contains
  · intro point cell equal
    have hx := congrArg Prod.fst equal
    have hy := congrArg Prod.snd equal
    apply Prod.ext <;> simp only [realCell,Cell.add,Int.cast_add,Prod.fst,Prod.snd] at hx hy ⊢ <;> linarith

theorem IsRealOpenSimple.translate {route : List Cell} (simple : IsRealOpenSimple route) (offset : Cell) :
    IsRealOpenSimple (translatePolyline offset route) := by
  apply simple.map (Cell.add offset) (add_injective offset)
    (fun point => (point.1-offset.1,point.2-offset.2))
  · intro segment point contains
    have shifted := GridSegment.realContains_translate segment offset (point.1-offset.1,point.2-offset.2)
    apply shifted.mp
    simpa [GridSegment.mapPoints,GridSegment.translate,Cell.add,add_comm] using contains
  · intro point cell equal
    have hx := congrArg Prod.fst equal
    have hy := congrArg Prod.snd equal
    apply Prod.ext <;> simp only [realCell,Cell.add,Int.cast_add,Prod.fst,Prod.snd] at hx hy ⊢ <;> linarith

theorem IsRealSimple.scale {route : List Cell} (simple : IsRealSimple route) {factor : Int} (nonzero : factor ≠ 0) :
    IsRealSimple (scalePolyline factor route) := by
  have realNonzero : (factor : ℝ) ≠ 0 := by exact_mod_cast nonzero
  apply simple.map (Cell.scale factor) (Cell.scale_injective nonzero)
    (fun point => (point.1/(factor : ℝ),point.2/(factor : ℝ)))
  · intro segment point contains
    exact (GridSegment.realContains_scale_inverse segment nonzero point).mp contains
  · intro point cell equal
    have hx := congrArg Prod.fst equal
    have hy := congrArg Prod.snd equal
    apply Prod.ext
    · simpa [realCell,Cell.scale,mul_comm] using (div_eq_iff realNonzero).mp hx
    · simpa [realCell,Cell.scale,mul_comm] using (div_eq_iff realNonzero).mp hy

end LeanTrominoes.GridPolyline
