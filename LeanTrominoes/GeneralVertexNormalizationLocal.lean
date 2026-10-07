/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GeneralVertexNormalizationDrawing

/-! # Vertex normalization preserves real locality -/
namespace LeanTrominoes.GeneralVertexNormalization
open PeriodicOrthocrossing
variable {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}

theorem fanAt_in_cell (valid : drawing.IsCompatible graph) (chosen : Vertex → GraphPort Vertex)
    {port : GraphPort Vertex} (member : port ∈ allPorts graph) (cell : Cell) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (fanAt graph drawing chosen port (liftedVertex graph drawing port.vertex cell)) point) :
    (normalizedDrawing graph drawing chosen).RealPointInCell cell point := by
  have bounds := fanAt_real_bounds graph drawing chosen port _ contains
  have vertexBounds := valid.2.2.2.2.1 _ (valid.vertexPosition_mem (port_vertex_mem valid.1 member))
  unfold PeriodicGridDrawing.PositionInFundamentalSquare at vertexBounds
  have xl : (1 : Int) ≤ (drawing.vertexPosition graph port.vertex).1 := by omega
  have xu : (drawing.vertexPosition graph port.vertex).1 ≤ (drawing.gridSize : Int)-1 := by omega
  have yl : (1 : Int) ≤ (drawing.vertexPosition graph port.vertex).2 := by omega
  have yu : (drawing.vertexPosition graph port.vertex).2 ≤ (drawing.gridSize : Int)-1 := by omega
  have xlr : (1 : ℝ) ≤ ((drawing.vertexPosition graph port.vertex).1 : ℝ) := by exact_mod_cast xl
  have xur : ((drawing.vertexPosition graph port.vertex).1 : ℝ) ≤ (drawing.gridSize : ℝ)-1 := by exact_mod_cast xu
  have ylr : (1 : ℝ) ≤ ((drawing.vertexPosition graph port.vertex).2 : ℝ) := by exact_mod_cast yl
  have yur : ((drawing.vertexPosition graph port.vertex).2 : ℝ) ≤ (drawing.gridSize : ℝ)-1 := by exact_mod_cast yu
  simp only [liftedVertex,PeriodicGridDrawing.periodTranslation,Cell.add,Cell.scale,Int.cast_add,Int.cast_mul,Int.cast_natCast] at bounds
  unfold PeriodicGridDrawing.RealPointInCell
  rw [normalizedDrawing_gridSize]
  simp only [Nat.cast_mul,Nat.cast_ofNat,Int.cast_zero,Int.cast_add,Int.cast_one]
  refine ⟨?_,?_,?_,?_⟩ <;> nlinarith [bounds.1,bounds.2.1,bounds.2.2.1,bounds.2.2.2]

theorem normalizedDrawing_cell_of_divide (chosen : Vertex → GraphPort Vertex) (cell : Cell) {point : ℝ × ℝ}
    (bounds : drawing.RealPointInCell cell (point.1/32,point.2/32)) :
    (normalizedDrawing graph drawing chosen).RealPointInCell cell point := by
  unfold PeriodicGridDrawing.RealPointInCell at bounds ⊢
  rw [normalizedDrawing_gridSize]
  simp only [Nat.cast_mul,Nat.cast_ofNat,Prod.fst,Prod.snd] at bounds ⊢
  refine ⟨?_,?_,?_,?_⟩ <;> nlinarith [bounds.1,bounds.2.1,bounds.2.2.1,bounds.2.2.2]

theorem normalizedDrawing_isRealLocal (valid : drawing.IsRealDrawing graph) (orthogonal : drawing.IsOrthogonal)
    (distinct : DistinctPortSides drawing graph) (isLocal : drawing.IsRealLocal graph) (chosen : Vertex → GraphPort Vertex) :
    (normalizedDrawing graph drawing chosen).IsRealLocal graph := by
  intro tagged member point contains
  rw [normalizedDrawing_edgeRoute chosen member] at contains
  rcases (normalizedRoute_realContains_parts valid orthogonal distinct chosen member (0,0) point).mp contains with
    (first | middle) | last
  · exact Or.inl (fanAt_in_cell valid.1 chosen (sourcePort_mem_allPorts graph member) (0,0) first)
  · have oldOrthogonal := liftedRoute_orthogonal valid.1 orthogonal member (0,0)
    have original := (GridPolyline.realContains_scale_inverse _ (by norm_num : (32 : Int) ≠ 0) _).mp
      (GridPolyline.clippedScaledRoute_realContains_source oldOrthogonal middle)
    have zero : drawing.realEdgeRoute tagged.2 (0,0) = drawing.edgeRoute tagged.2 := by
      change translatePolyline (drawing.periodTranslation (0,0)) (drawing.edgeRoute tagged.2) = _
      rw [show drawing.periodTranslation (0,0) = (0,0) by simp [PeriodicGridDrawing.periodTranslation,Cell.scale],translatePolyline_zero]
    rw [zero] at original
    rcases isLocal tagged member _ original with firstBounds | lastBounds
    · exact Or.inl (normalizedDrawing_cell_of_divide chosen (0,0) firstBounds)
    · exact Or.inr (normalizedDrawing_cell_of_divide chosen tagged.1.offset lastBounds)
  · apply Or.inr
    apply fanAt_in_cell valid.1 chosen (targetPort_mem_allPorts graph member) tagged.1.offset
    simpa [targetFan,targetPort,Cell.add] using last

end LeanTrominoes.GeneralVertexNormalization
