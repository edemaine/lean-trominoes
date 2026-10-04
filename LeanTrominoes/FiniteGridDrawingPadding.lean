/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingExpandedBounds
import LeanTrominoes.PeriodicGridDrawingScaling
import LeanTrominoes.PeriodicThreeDMContractionPlanarity

/-! # Padding a finite zero-offset grid drawing inside a larger square -/
namespace LeanTrominoes.PeriodicGridDrawing
open PeriodicOrthocrossing

def finitePaddingOffset (drawing : PeriodicGridDrawing) : Cell :=
  (drawing.gridSize,drawing.gridSize)

def finitePad (drawing : PeriodicGridDrawing) : PeriodicGridDrawing where
  gridSizePred := 3*drawing.gridSize
  vertexPositions := drawing.vertexPositions.map (Cell.add drawing.finitePaddingOffset)
  edgeRoutes := drawing.edgeRoutes.map (translatePolyline drawing.finitePaddingOffset)

@[simp] theorem finitePad_gridSize (drawing : PeriodicGridDrawing) :
    drawing.finitePad.gridSize=3*drawing.gridSize+1 := rfl

def finitePadIndexed (drawing : PeriodicGridDrawing) (indexed : IndexedGridSegment) : IndexedGridSegment :=
  ⟨indexed.routeIndex,indexed.segmentIndex,indexed.segment.translate drawing.finitePaddingOffset⟩

theorem finitePad_indexedSegments (drawing : PeriodicGridDrawing) :
    drawing.finitePad.indexedSegments=drawing.indexedSegments.map drawing.finitePadIndexed := by
  unfold indexedSegments finitePad
  rw [List.zipIdx_map,List.flatMap_map,List.map_flatMap]
  apply List.flatMap_congr
  rintro ⟨route,index⟩ _
  simp [gridPolylineSegments_translatePolyline,List.zipIdx_map,List.map_map,
    finitePadIndexed,Function.comp_def]

theorem finitePad_point_inFundamental {drawing : PeriodicGridDrawing} {point : Cell}
    (inside : drawing.PositionInExpandedSquare point) :
    drawing.finitePad.PositionInFundamentalSquare (Cell.add drawing.finitePaddingOffset point) := by
  simp only [PositionInExpandedSquare] at inside
  simp only [PositionInFundamentalSquare,finitePad_gridSize,finitePaddingOffset,Cell.add]
  norm_num only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  omega

theorem finitePad_segmentEndpoints {drawing : PeriodicGridDrawing}
    (inside : drawing.SegmentEndpointsInExpandedSquare) :
    drawing.finitePad.SegmentEndpointsInFundamentalSquare := by
  intro indexed member
  rw [finitePad_indexedSegments] at member
  obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
  exact ⟨finitePad_point_inFundamental (inside original originalMember).1,
    finitePad_point_inFundamental (inside original originalMember).2⟩

theorem finitePad_isOrthogonal {drawing : PeriodicGridDrawing} (orthogonal : drawing.IsOrthogonal) :
    drawing.finitePad.IsOrthogonal := by
  intro indexed member
  rw [finitePad_indexedSegments] at member
  obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
  exact (GridSegment.isAxisAligned_translate _ _).mpr (orthogonal _ originalMember)

theorem finitePad_edgeRoute (drawing : PeriodicGridDrawing) (index : Nat) :
    drawing.finitePad.edgeRoute index=translatePolyline drawing.finitePaddingOffset (drawing.edgeRoute index) := by
  unfold edgeRoute finitePad
  change (drawing.edgeRoutes.map (translatePolyline drawing.finitePaddingOffset)).getD index
    (translatePolyline drawing.finitePaddingOffset [])=_
  rw [List.getD_map]

theorem finitePad_vertexPosition {V : Type*} [DecidableEq V] (drawing : PeriodicGridDrawing)
    (graph : PeriodicGraph V) (lengthEq : drawing.vertexPositions.length=graph.vertices.length)
    (vertex : V) (member : vertex∈graph.vertices) :
    drawing.finitePad.vertexPosition graph vertex=Cell.add drawing.finitePaddingOffset (drawing.vertexPosition graph vertex) := by
  have indexLt : graph.vertices.idxOf vertex<drawing.vertexPositions.length := by
    rw [lengthEq]
    exact List.idxOf_lt_length_iff.mpr member
  simp only [vertexPosition,finitePad]
  rw [List.getD_eq_getElem _ _ (by simpa using indexLt),List.getD_eq_getElem _ _ indexLt,List.getElem_map]

theorem finitePad_isCompatible {V : Type*} [DecidableEq V] {drawing : PeriodicGridDrawing}
    {graph : PeriodicGraph V} (compatible : drawing.IsCompatible graph)
    (zero : ∀ edge∈graph.edges,edge.offset=(0,0)) : drawing.finitePad.IsCompatible graph := by
  obtain ⟨wellFormed,vertexLength,routeLength,nodup,bounds,routes⟩ := compatible
  refine ⟨wellFormed,by simpa [finitePad] using vertexLength,
    by simpa [finitePad] using routeLength,?_,?_,?_⟩
  · apply nodup.map
    intro first second eq
    apply Prod.ext
    · exact add_left_cancel (congrArg Prod.fst eq)
    · exact add_left_cancel (congrArg Prod.snd eq)
  · intro point member
    obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
    exact finitePad_point_inFundamental (positionInExpandedSquare_of_fundamental (bounds _ originalMember))
  · intro tagged member
    have edgeMember := List.fst_mem_of_mem_zipIdx member
    have edgeZero := zero tagged.1 edgeMember
    have endpoints := routes tagged member
    have sourceMember := (wellFormed.2 tagged.1 edgeMember).1
    have targetMember := (wellFormed.2 tagged.1 edgeMember).2
    rw [finitePad_edgeRoute]
    constructor
    · rw [show (translatePolyline drawing.finitePaddingOffset (drawing.edgeRoute tagged.2)).head?=
        (drawing.edgeRoute tagged.2).head?.map (Cell.add drawing.finitePaddingOffset) by
          cases drawing.edgeRoute tagged.2 <;> rfl,endpoints.1]
      rw [finitePad_vertexPosition drawing graph vertexLength _ sourceMember]
      rfl
    · rw [show (translatePolyline drawing.finitePaddingOffset (drawing.edgeRoute tagged.2)).getLast?=
        (drawing.edgeRoute tagged.2).getLast?.map (Cell.add drawing.finitePaddingOffset) by
          simp [translatePolyline],endpoints.2]
      rw [finitePad_vertexPosition drawing graph vertexLength _ targetMember]
      simp [edgeZero,periodTranslation,Cell.scale,Cell.add]
end LeanTrominoes.PeriodicGridDrawing
