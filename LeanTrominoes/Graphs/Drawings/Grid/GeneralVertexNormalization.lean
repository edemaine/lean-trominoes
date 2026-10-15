/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.GeneralVertexNormalizationRealDrawing
import LeanTrominoes.Graphs.Drawings.Grid.GeneralVertexNormalizationDirections
import LeanTrominoes.Graphs.Drawings.Grid.GeneralVertexNormalizationLocal

/-! # Lemma 2.3: normalize selected incidences of a planar orthogonal drawing

The construction multiplies every grid coordinate and the period by 32.
Thus it preserves the rational vertex placements and every edge's lattice
offset. At degree-three vertices the three outward directions are west,
north, east, and the selected incidence points west. Real simplicity,
planarity, and locality are preserved, including loops and isolated vertices.
-/
namespace LeanTrominoes.GeneralVertexNormalization
open PeriodicOrthocrossing

def SelectedIncidences {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (chosen : Vertex → GraphPort Vertex) : Prop :=
  ∀ vertex ∈ graph.vertices, (portsAt graph vertex).length = 3 → chosen vertex ∈ portsAt graph vertex

def IsNormalized {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (drawing : PeriodicGridDrawing) (chosen : Vertex → GraphPort Vertex) : Prop :=
  (∀ port ∈ allPorts graph, (portsAt graph port.vertex).length = 3 →
    portDirection drawing port = .west ∨ portDirection drawing port = .north ∨ portDirection drawing port = .east) ∧
  ∀ vertex ∈ graph.vertices, (portsAt graph vertex).length = 3 → portDirection drawing (chosen vertex) = .west

theorem normalizedDrawing_isNormalized {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph) (orthogonal : drawing.IsOrthogonal)
    (chosen : Vertex → GraphPort Vertex) (selection : SelectedIncidences graph chosen) :
    IsNormalized graph (normalizedDrawing graph drawing chosen) chosen := by
  refine ⟨fun port member degree => normalizedDrawing_degree_three_directions planar orthogonal chosen member degree,?_⟩
  intro vertex member degree
  have chosenMember : chosen vertex ∈ allPorts graph ∧ (chosen vertex).vertex = vertex := by
    simpa [portsAt] using selection vertex member degree
  exact normalizedDrawing_chosen_west planar orthogonal chosen vertex chosenMember.1 chosenMember.2 degree

theorem lemma23 {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph) (orthogonal : drawing.IsOrthogonal)
    (chosen : Vertex → GraphPort Vertex) (selection : SelectedIncidences graph chosen) :
    ∃ result : PeriodicGridDrawing,
      result.IsRealPlanarDrawing graph ∧ result.IsOrthogonal ∧ IsNormalized graph result chosen ∧
      result.gridSize = 32*drawing.gridSize ∧
      result.vertexPositions = drawing.vertexPositions.map (Cell.scale 32) ∧
      (drawing.IsRealLocal graph → result.IsRealLocal graph) := by
  have distinct := distinctPortSides_of_planar_orthogonal planar orthogonal
  exact ⟨normalizedDrawing graph drawing chosen,normalizedDrawing_isRealPlanarDrawing planar orthogonal chosen,
    normalizedDrawing_orthogonal planar.1 orthogonal distinct chosen,
    normalizedDrawing_isNormalized planar orthogonal chosen selection,normalizedDrawing_gridSize chosen,rfl,
    fun isLocal => normalizedDrawing_isRealLocal planar.1 orthogonal distinct isLocal chosen⟩

end LeanTrominoes.GeneralVertexNormalization
