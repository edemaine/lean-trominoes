/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.GeneralVertexNormalizationRouteProperties

/-! # The drawing produced by uncolored vertex normalization -/
namespace LeanTrominoes.GeneralVertexNormalization
open PeriodicOrthocrossing

def normalizedDrawing {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (drawing : PeriodicGridDrawing) (chosen : Vertex → GraphPort Vertex) : PeriodicGridDrawing where
  gridSizePred := 32*drawing.gridSize-1
  vertexPositions := drawing.vertexPositions.map (Cell.scale 32)
  edgeRoutes := graph.edges.zipIdx.map (fun tagged => normalizedRoute graph drawing chosen tagged (0,0))

variable {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}

theorem normalizedDrawing_gridSize (chosen : Vertex → GraphPort Vertex) :
    (normalizedDrawing graph drawing chosen).gridSize = 32*drawing.gridSize := by
  simp only [normalizedDrawing,PeriodicGridDrawing.gridSize]
  omega

theorem normalizedDrawing_periodTranslation (chosen : Vertex → GraphPort Vertex) (cell : Cell) :
    (normalizedDrawing graph drawing chosen).periodTranslation cell = Cell.scale 32 (drawing.periodTranslation cell) := by
  rw [PeriodicGridDrawing.periodTranslation,normalizedDrawing_gridSize]
  apply Prod.ext <;> simp [PeriodicGridDrawing.periodTranslation,Cell.scale] <;> ring

theorem normalizedDrawing_vertexPosition (chosen : Vertex → GraphPort Vertex) (vertex : Vertex) :
    (normalizedDrawing graph drawing chosen).vertexPosition graph vertex = Cell.scale 32 (drawing.vertexPosition graph vertex) := by
  unfold PeriodicGridDrawing.vertexPosition
  change (drawing.vertexPositions.map (Cell.scale 32)).getD (graph.vertices.idxOf vertex) (Cell.scale 32 (0,0)) = _
  exact List.getD_map drawing.vertexPositions (0,0) (Cell.scale 32)

theorem normalizedDrawing_edgeRoute (chosen : Vertex → GraphPort Vertex) {tagged : PeriodicEdge Vertex × Nat}
    (member : tagged ∈ graph.edges.zipIdx) :
    (normalizedDrawing graph drawing chosen).edgeRoute tagged.2 = normalizedRoute graph drawing chosen tagged (0,0) := by
  have originalAt := List.mem_zipIdx_iff_getElem?.mp member
  have taggedAt : graph.edges.zipIdx[tagged.2]? = some tagged := by
    rw [List.getElem?_zipIdx,originalAt]
    simp
  have currentAt : (normalizedDrawing graph drawing chosen).edgeRoutes[tagged.2]? =
      some (normalizedRoute graph drawing chosen tagged (0,0)) := by
    change (graph.edges.zipIdx.map (fun tagged => normalizedRoute graph drawing chosen tagged (0,0)))[tagged.2]? = _
    rw [List.getElem?_map,taggedAt]
    rfl
  simp only [PeriodicGridDrawing.edgeRoute,List.getD_eq_getElem?_getD,currentAt,Option.getD_some]

theorem normalizedDrawing_realEdgeRoute (chosen : Vertex → GraphPort Vertex) {tagged : PeriodicEdge Vertex × Nat}
    (member : tagged ∈ graph.edges.zipIdx) (cell : Cell) :
    (normalizedDrawing graph drawing chosen).realEdgeRoute tagged.2 cell = normalizedRoute graph drawing chosen tagged cell := by
  rw [PeriodicGridDrawing.realEdgeRoute,normalizedDrawing_edgeRoute chosen member,
    normalizedDrawing_periodTranslation,normalizedRoute_translate chosen tagged cell]
  rfl

theorem normalizedDrawing_compatible (valid : drawing.IsCompatible graph) (chosen : Vertex → GraphPort Vertex) :
    (normalizedDrawing graph drawing chosen).IsCompatible graph := by
  refine ⟨valid.1,?_,?_,?_,?_,?_⟩
  · simpa [normalizedDrawing] using valid.2.1
  · simp [normalizedDrawing]
  · exact valid.2.2.2.1.map (Cell.scale_injective (by norm_num : (32 : Int) ≠ 0))
  · intro position member
    obtain ⟨old,oldMember,rfl⟩ := List.mem_map.mp member
    have bounds := valid.2.2.2.2.1 old oldMember
    unfold PeriodicGridDrawing.PositionInFundamentalSquare at bounds ⊢
    rw [normalizedDrawing_gridSize]
    simp only [Cell.scale,Nat.cast_mul,Nat.cast_ofNat]
    omega
  · intro tagged member
    rw [normalizedDrawing_edgeRoute chosen member,normalizedDrawing_vertexPosition,
      normalizedDrawing_vertexPosition,normalizedDrawing_periodTranslation]
    have endpoints := normalizedRoute_endpoints (graph := graph) (drawing := drawing) chosen tagged (0,0)
    constructor
    · simpa [liftedVertex,PeriodicGridDrawing.periodTranslation,Cell.scale,Cell.add] using endpoints.1
    · simpa [liftedVertex,PeriodicGridDrawing.periodTranslation,Cell.scale,Cell.add,mul_add] using endpoints.2

end LeanTrominoes.GeneralVertexNormalization
