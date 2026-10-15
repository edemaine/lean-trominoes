/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.GeneralVertexNormalizationCoreContacts
import LeanTrominoes.Graphs.Drawings.Grid.GeneralVertexNormalizationRouteProperties

/-! # Distinct normalized edge occurrences meet only at graph endpoints -/
namespace LeanTrominoes.GeneralVertexNormalization
open PeriodicOrthocrossing
variable {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}

def endpointFan (chosen : Vertex → GraphPort Vertex) (tagged : PeriodicEdge Vertex × Nat) (cell : Cell) (target : Bool) : List Cell :=
  fanAt graph drawing chosen (endpointPort tagged target)
    (liftedVertex graph drawing (endpointPort tagged target).vertex (portCell tagged cell target))

theorem normalizedRoute_realContains_either (valid : drawing.IsRealDrawing graph) (orthogonal : drawing.IsOrthogonal)
    (distinct : DistinctPortSides drawing graph) (chosen : Vertex → GraphPort Vertex)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) (cell : Cell) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (normalizedRoute graph drawing chosen tagged cell) point) :
    GridPolyline.RealContains (trimmedCore drawing tagged.2 cell) point ∨
      ∃ target : Bool, GridPolyline.RealContains (endpointFan (graph := graph) (drawing := drawing) chosen tagged cell target) point := by
  rcases (normalizedRoute_realContains_parts valid orthogonal distinct chosen member cell point).mp contains with
    (first | middle) | last
  · exact Or.inr ⟨false,first⟩
  · exact Or.inl middle
  · exact Or.inr ⟨true,last⟩

theorem normalizedRoute_endpoint_of_fan_center (chosen : Vertex → GraphPort Vertex)
    (tagged : PeriodicEdge Vertex × Nat) (cell : Cell) (target : Bool) {point : ℝ × ℝ}
    (equal : point = realCell (Cell.scale 32
      (liftedVertex graph drawing (endpointPort tagged target).vertex (portCell tagged cell target)))) :
    GridPolyline.RealIsEndpoint (normalizedRoute graph drawing chosen tagged cell) point := by
  have endpoints := normalizedRoute_endpoints (graph := graph) (drawing := drawing) chosen tagged cell
  cases target
  · exact Or.inl ⟨_,endpoints.1,equal⟩
  · exact Or.inr ⟨_,endpoints.2,equal⟩

theorem normalized_route_occurrences_contacts (planar : drawing.IsRealPlanarDrawing graph) (orthogonal : drawing.IsOrthogonal)
    (distinct : DistinctPortSides drawing graph) (chosen : Vertex → GraphPort Vertex)
    {a b : PeriodicEdge Vertex × Nat} (am : a ∈ graph.edges.zipIdx) (bm : b ∈ graph.edges.zipIdx)
    (aCell bCell : Cell) (different : (a.2,aCell) ≠ (b.2,bCell)) {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains (normalizedRoute graph drawing chosen a aCell) point)
    (secondContains : GridPolyline.RealContains (normalizedRoute graph drawing chosen b bCell) point) :
    GridPolyline.RealIsEndpoint (normalizedRoute graph drawing chosen a aCell) point ∧
      GridPolyline.RealIsEndpoint (normalizedRoute graph drawing chosen b bCell) point := by
  have firstParts := normalizedRoute_realContains_either planar.1 orthogonal distinct chosen am aCell firstContains
  have secondParts := normalizedRoute_realContains_either planar.1 orthogonal distinct chosen bm bCell secondContains
  rcases firstParts with firstCore | ⟨aTarget,firstFan⟩
  · rcases secondParts with secondCore | ⟨bTarget,secondFan⟩
    · exact (trimmed_cores_disjoint planar orthogonal am bm aCell bCell different firstCore secondCore).elim
    · exact (different (fan_core_occurrence_contact planar.1 orthogonal distinct chosen bm am bTarget bCell aCell
        secondFan firstCore).symm).elim
  · rcases secondParts with secondCore | ⟨bTarget,secondFan⟩
    · exact (different (fan_core_occurrence_contact planar.1 orthogonal distinct chosen am bm aTarget aCell bCell
        firstFan secondCore)).elim
    · have fm := endpointPort_mem graph am aTarget
      have sm := endpointPort_mem graph bm bTarget
      have contact := fan_occurrence_contacts planar.1.1 distinct chosen fm sm firstFan secondFan
      rcases contact.2.2 with ports | center
      · exact (different (endpoint_occurrence_injective am bm ports contact.2.1)).elim
      · have positions : liftedVertex graph drawing (endpointPort a aTarget).vertex (portCell a aCell aTarget) =
          liftedVertex graph drawing (endpointPort b bTarget).vertex (portCell b bCell bTarget) :=
          congrArg₂ (liftedVertex graph drawing) contact.1 contact.2.1
        exact ⟨normalizedRoute_endpoint_of_fan_center chosen a aCell aTarget center,
          normalizedRoute_endpoint_of_fan_center chosen b bCell bTarget
            (center.trans (congrArg (fun position => realCell (Cell.scale 32 position)) positions))⟩

end LeanTrominoes.GeneralVertexNormalization
