/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentScaledEndpointTrim
import LeanTrominoes.GridPolylineSegmentIndices

/-! # Indexed provenance of a route with trimmed scaled endpoints -/
namespace LeanTrominoes.GridPolyline

def clippedScaledPoint (route : List Cell) (index : Nat) (point : Cell) : Cell :=
  if index = 0 then
    Cell.add (Cell.scale 32 point)
      (Cell.scale 8 (AxisDirection.between point (route[1]?.getD point)).step)
  else if index+1 = route.length then
    Cell.add (Cell.scale 32 point)
      (Cell.scale (-8) (AxisDirection.between (route[index-1]?.getD point) point).step)
  else Cell.scale 32 point

def clippedScaledRoute (route : List Cell) : List Cell := route.mapIdx (clippedScaledPoint route)
def firstTrimCut (index : Nat) : Int := if index = 0 then 8 else 0
def lastTrimCut (count index : Nat) : Int := if index+1 = count then 8 else 0

theorem clippedScaledRoute_length (route : List Cell) : (clippedScaledRoute route).length = route.length := by
  simp [clippedScaledRoute]

theorem clippedScaledRoute_segments_length (route : List Cell) :
    (gridPolylineSegments (clippedScaledRoute route)).length = (gridPolylineSegments route).length := by
  simp [gridPolylineSegments_length,clippedScaledRoute_length]

theorem clippedScaledRoute_piece_of_indexed {route : List Cell} {tagged : GridSegment × Nat}
    (member : tagged ∈ (gridPolylineSegments route).zipIdx) :
    (gridPolylineSegments (clippedScaledRoute route))[tagged.2]? =
      some (tagged.1.trimScaled (firstTrimCut tagged.2) (lastTrimCut (gridPolylineSegments route).length tagged.2)) := by
  have ends := indexed_gridPolylineSegment_endpoints member
  have valid := List.snd_lt_of_mem_zipIdx member
  have count := gridPolylineSegments_length route
  have startNotLast : tagged.2+1 ≠ route.length := by omega
  apply (gridPolylineSegments_getElem?_eq_some_iff _ _ _).mpr
  constructor
  · rw [clippedScaledRoute,List.getElem?_mapIdx,ends.1,Option.map_some]
    congr 1
    by_cases first : tagged.2 = 0
    · have next : route[1]? = some tagged.1.finish := by simpa [first] using ends.2
      simp [clippedScaledPoint,firstTrimCut,GridSegment.trimScaled,first,next,Cell.scale,Cell.add]
    · simp [clippedScaledPoint,firstTrimCut,GridSegment.trimScaled,first,startNotLast,Cell.scale,Cell.add]
  · rw [clippedScaledRoute,List.getElem?_mapIdx,ends.2,Option.map_some]
    congr 1
    have positive : tagged.2+1 ≠ 0 := by omega
    by_cases last : tagged.2+1 = (gridPolylineSegments route).length
    · have lastPoint : tagged.2+1+1 = route.length := by omega
      simp only [clippedScaledPoint,positive,ite_false,lastPoint,ite_true,Nat.add_sub_cancel,ends.1,Option.getD_some]
      simp [lastTrimCut,GridSegment.trimScaled,last,Cell.scale,Cell.add]
    · have notLastPoint : tagged.2+1+1 ≠ route.length := by omega
      simp only [clippedScaledPoint,positive,ite_false,notLastPoint]
      simp [lastTrimCut,GridSegment.trimScaled,last,Cell.scale,Cell.add]

theorem clippedScaledRoute_piece_has_original {route : List Cell} {tagged : GridSegment × Nat}
    (member : tagged ∈ (gridPolylineSegments (clippedScaledRoute route)).zipIdx) :
    ∃ original ∈ (gridPolylineSegments route).zipIdx, original.2 = tagged.2 ∧
      tagged.1 = original.1.trimScaled (firstTrimCut original.2) (lastTrimCut (gridPolylineSegments route).length original.2) := by
  have bound : tagged.2 < (gridPolylineSegments route).length := by
    simpa [clippedScaledRoute_segments_length] using List.snd_lt_of_mem_zipIdx member
  let original := (gridPolylineSegments route)[tagged.2]'bound
  have originalAt : (gridPolylineSegments route)[tagged.2]? = some original := by
    rw [List.getElem?_eq_some_iff]
    exact ⟨bound,rfl⟩
  have originalMember : (original,tagged.2) ∈ (gridPolylineSegments route).zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr originalAt
  refine ⟨(original,tagged.2),originalMember,rfl,?_⟩
  have originalPiece := clippedScaledRoute_piece_of_indexed originalMember
  have currentPiece := List.mem_zipIdx_iff_getElem?.mp member
  exact Option.some.inj (currentPiece.symm.trans originalPiece)

end LeanTrominoes.GridPolyline
