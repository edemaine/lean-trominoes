/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.GeneralVertexNormalizationRouteContacts

/-! # Normalized routes avoid every nonincident lifted vertex -/
namespace LeanTrominoes.GeneralVertexNormalization
open PeriodicOrthocrossing
variable {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}

theorem fanAt_contains_scaled_grid_point (chosen : Vertex → GraphPort Vertex) (port : GraphPort Vertex)
    {position anchor : Cell}
    (contains : GridPolyline.RealContains (fanAt graph drawing chosen port position) (realCell (Cell.scale 32 anchor))) :
    position = anchor := by
  have bounds := fanAt_real_bounds graph drawing chosen port position contains
  apply Prod.ext
  · apply GridSegment.closed_interval_periodic_shifts_unique (period := 32) (lower := -8) (upper := 8)
      (point := (realCell (Cell.scale 32 anchor)).1) (by norm_num) (by norm_num)
    · simpa using And.intro bounds.1 bounds.2.1
    · simp [realCell,Cell.scale]
  · apply GridSegment.closed_interval_periodic_shifts_unique (period := 32) (lower := -8) (upper := 8)
      (point := (realCell (Cell.scale 32 anchor)).2) (by norm_num) (by norm_num)
    · simpa using And.intro bounds.2.2.1 bounds.2.2.2
    · simp [realCell,Cell.scale]

theorem normalizedRoute_vertexAvoidance (valid : drawing.IsRealDrawing graph) (orthogonal : drawing.IsOrthogonal)
    (distinct : DistinctPortSides drawing graph) (chosen : Vertex → GraphPort Vertex)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    {vertex : Cell} (vertexMember : vertex ∈ drawing.vertexPositions) (vertexCell edgeCell : Cell)
    (contains : GridPolyline.RealContains (normalizedRoute graph drawing chosen tagged edgeCell)
      (realCell (Cell.scale 32 (Cell.add vertex (drawing.periodTranslation vertexCell))))) :
    GridPolyline.RealIsEndpoint (normalizedRoute graph drawing chosen tagged edgeCell)
      (realCell (Cell.scale 32 (Cell.add vertex (drawing.periodTranslation vertexCell)))) := by
  rcases normalizedRoute_realContains_either valid orthogonal distinct chosen member edgeCell contains with
    coreContains | ⟨target,fanContains⟩
  · have oldOrthogonal := liftedRoute_orthogonal valid.1 orthogonal member edgeCell
    have oldContains := (GridPolyline.realContains_scale_inverse _ (by norm_num : (32 : Int) ≠ 0) _).mp
      (GridPolyline.clippedScaledRoute_realContains_source oldOrthogonal coreContains)
    have realPoint :
        ((realCell (Cell.scale 32 (Cell.add vertex (drawing.periodTranslation vertexCell)))).1/(32 : Int),
          (realCell (Cell.scale 32 (Cell.add vertex (drawing.periodTranslation vertexCell)))).2/(32 : Int)) =
        realCell (Cell.add vertex (drawing.periodTranslation vertexCell)) := by
      simp [realCell,Cell.scale]
    rw [realPoint] at oldContains
    have validIndex : tagged.2 < drawing.edgeRoutes.length := by
      rw [valid.1.2.2.1]; exact List.snd_lt_of_mem_zipIdx member
    have endpoint := valid.2.2 vertex vertexMember vertexCell edgeCell tagged.2 validIndex oldContains
    exact (GridPolyline.clippedScaledRoute_not_contains_scaled_endpoint (liftedRoute_simple valid member edgeCell)
      oldOrthogonal endpoint coreContains).elim
  · have positionEq := fanAt_contains_scaled_grid_point chosen (endpointPort tagged target) fanContains
    apply normalizedRoute_endpoint_of_fan_center chosen tagged edgeCell target
    exact congrArg (fun position => realCell (Cell.scale 32 position)) positionEq.symm

end LeanTrominoes.GeneralVertexNormalization
