/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingBendSubdivisionLiftedPoints
import LeanTrominoes.PeriodicGridDrawingBendPerturbationPlanarity
import LeanTrominoes.PeriodicGridDrawingPolygonalPointOccurrences

/-! # Inserted bend vertices have distinct interior positions -/
namespace LeanTrominoes.PeriodicGridDrawing.BendSubdivision
open PeriodicGraph.BendSubdivision

theorem bend_position_ne_original {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    {factor : Nat} (spacing : 16*(drawing.gridSize:Int)+8 < (factor:Int))
    {edgeIndex pointIndex : Nat} {vertex : V}
    (bendMember : Vertex.bend edgeIndex pointIndex ∈ (subdivisionGraph source drawing factor).vertices)
    (originalMember : Vertex.original vertex ∈ (subdivisionGraph source drawing factor).vertices) :
    position source drawing factor (.bend edgeIndex pointIndex) ≠ position source drawing factor (.original vertex) := by
  have gridPositive : (0:Int) < drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have positive : 0 < factor := by omega
  have bounds := bend_vertex_mem_bounds planar.1.1 bendMember
  have movedPlanar := InteriorBends.perturbDrawing_planar planar localDrawing localGraph spacing
  have edgeValid : edgeIndex < (InteriorBends.perturbDrawing drawing factor).edgeRoutes.length := by
    simpa only [InteriorBends.perturbDrawing,List.length_map] using bounds.1
  have pointValid : pointIndex+1 < ((InteriorBends.perturbDrawing drawing factor).edgeRoute edgeIndex).length := by
    simpa only [moved_route_length] using bounds.2.2
  have listed := original_vertex_mem.mp originalMember
  have vertexMember : Cell.scale factor (drawing.vertexPosition source vertex) ∈
      (InteriorBends.perturbDrawing drawing factor).vertexPositions :=
    List.mem_map.mpr ⟨_,planar.1.1.vertexPosition_mem listed,rfl⟩
  have different := internal_route_point_avoids_vertex movedPlanar edgeValid bounds.2.1 pointValid vertexMember
    (bendCopy (V := V) drawing factor edgeIndex pointIndex) (0,0)
  rw [bend_lifted_representative source drawing positive bounds.2.2] at different
  simpa only [position,periodTranslation,Cell.scale,mul_zero,Cell.add,add_zero] using different

theorem bend_positions_injective {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    {factor : Nat} (spacing : 16*(drawing.gridSize:Int)+8 < (factor:Int))
    {firstEdge firstPoint secondEdge secondPoint : Nat}
    (firstMember : Vertex.bend firstEdge firstPoint ∈ (subdivisionGraph source drawing factor).vertices)
    (secondMember : Vertex.bend secondEdge secondPoint ∈ (subdivisionGraph source drawing factor).vertices)
    (equal : position source drawing factor (.bend firstEdge firstPoint)=position source drawing factor (.bend secondEdge secondPoint)) :
    (firstEdge,firstPoint)=(secondEdge,secondPoint) := by
  have gridPositive : (0:Int) < drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have positive : 0 < factor := by omega
  have firstBounds := bend_vertex_mem_bounds planar.1.1 firstMember
  have secondBounds := bend_vertex_mem_bounds planar.1.1 secondMember
  have movedPlanar := InteriorBends.perturbDrawing_planar planar localDrawing localGraph spacing
  have firstEdgeValid : firstEdge < (InteriorBends.perturbDrawing drawing factor).edgeRoutes.length := by
    simpa only [InteriorBends.perturbDrawing,List.length_map] using firstBounds.1
  have secondEdgeValid : secondEdge < (InteriorBends.perturbDrawing drawing factor).edgeRoutes.length := by
    simpa only [InteriorBends.perturbDrawing,List.length_map] using secondBounds.1
  have firstPointValid : firstPoint+1 < ((InteriorBends.perturbDrawing drawing factor).edgeRoute firstEdge).length := by
    simpa only [moved_route_length] using firstBounds.2.2
  have secondPointValid : secondPoint+1 < ((InteriorBends.perturbDrawing drawing factor).edgeRoute secondEdge).length := by
    simpa only [moved_route_length] using secondBounds.2.2
  have atFirst := bend_lifted_representative source drawing positive firstBounds.2.2
  have atSecond := bend_lifted_representative source drawing positive secondBounds.2.2
  have coordinates := atFirst.trans (equal.trans atSecond.symm)
  have keys := internal_route_point_occurrences_unique movedPlanar firstEdgeValid secondEdgeValid
    firstBounds.2.1 secondBounds.2.1 firstPointValid secondPointValid
    (bendCopy (V := V) drawing factor firstEdge firstPoint) (bendCopy (V := V) drawing factor secondEdge secondPoint) coordinates
  have edgeEq : firstEdge=secondEdge := congrArg (fun key : Nat × Nat × Cell => key.1) keys
  have pointEq : firstPoint=secondPoint := congrArg (fun key : Nat × Nat × Cell => key.2.1) keys
  exact Prod.ext edgeEq pointEq

theorem subdivision_vertexPositions_nodup {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    {factor : Nat} (spacing : 16*(drawing.gridSize:Int)+8 < (factor:Int)) :
    (subdivisionDrawing source drawing factor).vertexPositions.Nodup := by
  have gridPositive : (0:Int) < drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have factorNonzero : (factor:Int) ≠ 0 := by omega
  apply (subdivisionGraph_wellFormed planar.1.1.1 drawing factor).1.map_on
  intro first firstMember second secondMember equal
  cases first with
  | original first =>
      cases second with
      | original second =>
          have originalEqual := Cell.scale_injective factorNonzero equal
          exact congrArg Vertex.original (planar.1.1.vertexPosition_injective_on
            (original_vertex_mem.mp firstMember) (original_vertex_mem.mp secondMember) originalEqual)
      | bend edgeIndex pointIndex =>
          exact ((bend_position_ne_original planar localDrawing localGraph spacing secondMember firstMember) equal.symm).elim
  | bend firstEdge firstPoint =>
      cases second with
      | original second =>
          exact ((bend_position_ne_original planar localDrawing localGraph spacing firstMember secondMember) equal).elim
      | bend secondEdge secondPoint =>
          have indices := bend_positions_injective planar localDrawing localGraph spacing firstMember secondMember equal
          have edgeEq : firstEdge=secondEdge := congrArg Prod.fst indices
          have pointEq : firstPoint=secondPoint := congrArg Prod.snd indices
          rw [edgeEq,pointEq]

end LeanTrominoes.PeriodicGridDrawing.BendSubdivision
