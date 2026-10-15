/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingBendSubdivisionOccurrenceTransport
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingBendPerturbationPlanarity

/-! # Subdivision route occurrences meet only at endpoints -/
namespace LeanTrominoes.PeriodicGridDrawing.BendSubdivision
open PeriodicGraph.BendSubdivision

theorem subdivision_segment_contacts {V : Type*} [DecidableEq V]
    {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (localDrawing : drawing.IsRealLocal source)
    (localGraph : source.IsLocal) {factor : Nat}
    (spacing : 16*(drawing.gridSize:Int)+8 < (factor:Int))
    {first second : PeriodicEdge (Vertex V) × Nat}
    (firstMember : first ∈ (subdivisionGraph source drawing factor).edges.zipIdx)
    (secondMember : second ∈ (subdivisionGraph source drawing factor).edges.zipIdx)
    (firstCell secondCell : Cell) (different : (first.2,firstCell)≠(second.2,secondCell)) :
    GridSegment.EndpointContacts
      ((subdivisionSegment source drawing factor first.1).translate
        ((subdivisionDrawing source drawing factor).periodTranslation firstCell))
      ((subdivisionSegment source drawing factor second.1).translate
        ((subdivisionDrawing source drawing factor).periodTranslation secondCell)) := by
  have gridPositive : (0:Int) < drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have positive : 0 < factor := by omega
  have firstRecord := recordAt_mem (by simpa using List.snd_lt_of_mem_zipIdx firstMember)
  have secondRecord := recordAt_mem (by simpa using List.snd_lt_of_mem_zipIdx secondMember)
  have firstPiece := record_segment_in_moved_route planar firstRecord
  have secondPiece := record_segment_in_moved_route planar secondRecord
  rw [recordAt_edge firstMember] at firstPiece
  rw [recordAt_edge secondMember] at secondPiece
  have contacts := polygonal_segment_contacts
    (InteriorBends.perturbDrawing_planar planar localDrawing localGraph spacing)
    (edgeRoute_tagged_mem_of_lt (record_parent_index_valid planar.1.1 firstRecord))
    (edgeRoute_tagged_mem_of_lt (record_parent_index_valid planar.1.1 secondRecord))
    firstPiece secondPiece
    (Cell.sub firstCell (sourceCell drawing factor first.1.source))
    (Cell.sub secondCell (sourceCell drawing factor second.1.source))
    (lifted_record_keys_ne firstMember secondMember firstCell secondCell different)
  simpa only [← lifted_subdivision_segment_eq source drawing positive] using contacts

theorem subdivision_edge_tagged_of_route_index {V : Type*} [DecidableEq V]
    {source : PeriodicGraph V} {drawing : PeriodicGridDrawing} {factor index : Nat}
    (valid : index < (subdivisionDrawing source drawing factor).edgeRoutes.length) :
    ∃ edge, (edge,index) ∈ (subdivisionGraph source drawing factor).edges.zipIdx := by
  have edgeValid : index < (subdivisionGraph source drawing factor).edges.length := by
    simpa only [subdivisionDrawing,List.length_map] using valid
  exact ⟨_,List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem edgeValid)⟩

theorem subdivisionDrawing_routesMeetOnlyAtEndpoints {V : Type*} [DecidableEq V]
    {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (localDrawing : drawing.IsRealLocal source)
    (localGraph : source.IsLocal) {factor : Nat}
    (spacing : 16*(drawing.gridSize:Int)+8 < (factor:Int)) :
    (subdivisionDrawing source drawing factor).RealRoutesMeetOnlyAtEndpoints := by
  intro firstIndex secondIndex firstCell secondCell firstValid secondValid different p firstContains secondContains
  obtain ⟨first,firstMember⟩ := subdivision_edge_tagged_of_route_index firstValid
  obtain ⟨second,secondMember⟩ := subdivision_edge_tagged_of_route_index secondValid
  rw [subdivision_segment_image source drawing factor firstMember] at firstContains
  rw [subdivision_segment_image source drawing factor secondMember] at secondContains
  have endpoints := subdivision_segment_contacts planar localDrawing localGraph spacing firstMember secondMember
    firstCell secondCell different p firstContains secondContains
  rw [subdivision_segment_endpoints source drawing factor firstMember,
    subdivision_segment_endpoints source drawing factor secondMember]
  exact endpoints

end LeanTrominoes.PeriodicGridDrawing.BendSubdivision
