/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridPolylineRealSegmentContacts
import LeanTrominoes.Common.Geometry.GridPolylineRealAffineSimplicity
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingPointBounds

/-! # Real simplicity survives small perturbations of polygonal bends -/
namespace LeanTrominoes
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

namespace GridSegment

theorem mapPoints_oriented_start (segment : GridSegment) (transform : Cell → Cell) (backwards : Bool) :
    ((segment.mapPoints transform).oriented backwards).start=transform (segment.oriented backwards).start := by
  cases backwards <;> rfl

theorem endpointPerturbation_mapPoints {factor : Int} {segment : GridSegment} {transform : Cell → Cell}
    (start : PointPerturbation factor segment.start (transform segment.start))
    (finish : PointPerturbation factor segment.finish (transform segment.finish)) :
    EndpointPerturbation factor segment (segment.mapPoints transform) := ⟨start,finish⟩

end GridSegment

namespace GridPolyline

theorem IsRealSimple.perturb {route : List Cell} (simple : IsRealSimple route)
    {factor bound : Int} (boundPositive : 1≤bound) (spacing : 8*bound+8<factor)
    (transform : Cell → Cell)
    (perturbed : ∀ p∈route, GridSegment.PointPerturbation factor p (transform p))
    (directions : ∀ segment∈gridPolylineSegments route,
      |segment.direction.1|≤bound ∧ |segment.direction.2|≤bound) :
    IsRealSimple (route.map transform) := by
  have segmentPerturbed {segment : GridSegment} (member : segment∈gridPolylineSegments route) :
      GridSegment.EndpointPerturbation factor segment (segment.mapPoints transform) := by
    have endpoints := gridPolylineSegments_endpoints_mem member
    exact GridSegment.endpointPerturbation_mapPoints (perturbed _ endpoints.1) (perturbed _ endpoints.2)
  refine ⟨by simpa only [List.length_map] using simple.1,?_,?_⟩
  · intro segment member
    rw [gridPolylineSegments_map_points] at member
    obtain ⟨old,oldMember,rfl⟩ := List.mem_map.mp member
    exact GridSegment.endpointPerturbation_nonconstant (by omega) (simple.2.1 old oldMember) (segmentPerturbed oldMember)
  · intro first firstMember second secondMember ordered p firstContains secondContains
    rw [gridPolylineSegments_map_points,List.zipIdx_map] at firstMember secondMember
    obtain ⟨a,am,rfl⟩ := List.mem_map.mp firstMember
    obtain ⟨b,bm,rfl⟩ := List.mem_map.mp secondMember
    have aMember := List.fst_mem_of_mem_zipIdx am
    have bMember := List.fst_mem_of_mem_zipIdx bm
    have oldContacts := simple.segment_contacts am bm (ne_of_lt ordered)
    obtain ⟨aBack,bBack,sameStart,atFirst,_⟩ := GridSegment.perturbations_contact boundPositive spacing
      (simple.2.1 _ aMember) (simple.2.1 _ bMember) (directions _ aMember) (directions _ bMember)
      oldContacts (segmentPerturbed aMember) (segmentPerturbed bMember)
      (fun aBack bBack same => by
        rw [GridSegment.mapPoints_oriented_start,GridSegment.mapPoints_oriented_start]
        exact congrArg transform same)
      firstContains secondContains
    let oldPoint := (a.1.oriented aBack).start
    have aContains : a.1.RealContains (realCell oldPoint) :=
      (GridSegment.oriented_contains _ _ _).mp (GridSegment.realContains_start _)
    have bContains : b.1.RealContains (realCell oldPoint) := by
      rw [show oldPoint=(b.1.oriented bBack).start from sameStart]
      exact (GridSegment.oriented_contains _ _ _).mp (GridSegment.realContains_start _)
    rw [GridSegment.mapPoints_oriented_start] at atFirst
    change p=realCell (transform oldPoint) at atFirst
    rcases simple.2.2 a am b bm ordered (realCell oldPoint) aContains bContains with adjacent | closed
    · have atJoint := realCell_injective adjacent.2
      exact Or.inl ⟨adjacent.1,by simpa only [atJoint,Prod.map,GridSegment.mapPoints] using atFirst⟩
    · have atSource := realCell_injective closed.2.2.1
      have atTarget := realCell_injective closed.2.2.2
      refine Or.inr ⟨closed.1,?_,?_,?_⟩
      · simpa only [gridPolylineSegments_map_points,List.length_map,Prod.map,id_eq] using closed.2.1
      · simpa only [atSource,Prod.map,GridSegment.mapPoints] using atFirst
      · simpa only [atTarget,Prod.map,GridSegment.mapPoints] using atFirst

end GridPolyline
end LeanTrominoes
