/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingBendSubdivisionPointLookup
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingVertexCoverage
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingScaling

/-! # Bend subdivision without moving boundary points

Auxiliary vertices use residues in the half-open fundamental square. Their
positions may lie on its boundary, so this raw drawing is not claimed to
satisfy `IsCompatible`. A doubled drawing translated by `(1,1)` gives strict
interior representatives without changing the geometric directions. It is
used only to assign ports; the final construction keeps the raw positions.
-/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision

def cell (grid : Int) (point : Cell) : Cell := (point.1/grid,point.2/grid)
def representative (grid : Int) (point : Cell) : Cell := (point.1%grid,point.2%grid)

theorem representative_lift (grid : Int) (point : Cell) :
    Cell.add (representative grid point) (Cell.scale grid (cell grid point)) = point := by
  apply Prod.ext <;> dsimp [representative,cell,Cell.add,Cell.scale]
  · exact Int.emod_add_mul_ediv point.1 grid
  · exact Int.emod_add_mul_ediv point.2 grid

theorem representative_bounds {grid : Int} (positive : 0 < grid) (point : Cell) :
    0 ≤ (representative grid point).1 ∧ (representative grid point).1 < grid ∧
      0 ≤ (representative grid point).2 ∧ (representative grid point).2 < grid := by
  exact ⟨Int.emod_nonneg _ (ne_of_gt positive),Int.emod_lt_of_pos _ positive,
    Int.emod_nonneg _ (ne_of_gt positive),Int.emod_lt_of_pos _ positive⟩

def middle {V : Type*} (drawing : PeriodicGridDrawing) (tagged : PeriodicEdge V × Nat) : List (Vertex V × Cell) :=
  (BendSubdivision.internalPoints drawing tagged.2).map fun entry =>
    (.bend tagged.2 entry.2,cell drawing.gridSize entry.1)

def subdivisionGraph {V : Type*} (source : PeriodicGraph V) (drawing : PeriodicGridDrawing) :
    PeriodicGraph (Vertex V) := graph source (middle drawing)

def position {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) : Vertex V → Cell
  | .original vertex => drawing.vertexPosition source vertex
  | .bend edgeIndex pointIndex => representative drawing.gridSize
      ((drawing.edgeRoute edgeIndex).getD pointIndex (0,0))

def straightRoute {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) (edge : PeriodicEdge (Vertex V)) : List Cell :=
  [position source drawing edge.source,
    Cell.add (position source drawing edge.target) (Cell.scale drawing.gridSize edge.offset)]

def subdivisionDrawing {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) : PeriodicGridDrawing where
  gridSizePred := drawing.gridSizePred
  vertexPositions := (subdivisionGraph source drawing).vertices.map (position source drawing)
  edgeRoutes := (subdivisionGraph source drawing).edges.map (straightRoute source drawing)

def shiftedPosition {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) (vertex : Vertex V) : Cell :=
  Cell.add (1,1) (Cell.scale 2 (position source drawing vertex))

def shiftedRoute {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) (edge : PeriodicEdge (Vertex V)) : List Cell :=
  [shiftedPosition source drawing edge.source,
    Cell.add (shiftedPosition source drawing edge.target) (Cell.scale (2*drawing.gridSize) edge.offset)]

def shiftedDrawing {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) : PeriodicGridDrawing where
  gridSizePred := 2*drawing.gridSize-1
  vertexPositions := (subdivisionGraph source drawing).vertices.map (shiftedPosition source drawing)
  edgeRoutes := (subdivisionGraph source drawing).edges.map (shiftedRoute source drawing)

theorem shiftedDrawing_gridSize {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) : (shiftedDrawing source drawing).gridSize = 2*drawing.gridSize := by
  change 2*drawing.gridSize-1+1 = 2*drawing.gridSize
  exact Nat.sub_add_cancel (by unfold gridSize; omega)

theorem middle_only_bends {V : Type*} (drawing : PeriodicGridDrawing) (edge : PeriodicEdge V × Nat)
    {entry : Vertex V × Cell} (member : entry ∈ middle drawing edge) : ∃ i j, entry.1 = Vertex.bend i j := by
  obtain ⟨point,_,rfl⟩ := List.mem_map.mp member
  exact ⟨edge.2,point.2,rfl⟩

theorem middle_indices_unique {V : Type*} (source : PeriodicGraph V) (drawing : PeriodicGridDrawing) :
    (source.edges.zipIdx.flatMap fun edge => (middle drawing edge).map Prod.fst).Nodup := by
  simpa only [middle,BendSubdivision.middle,List.map_map,Function.comp_def] using
    BendSubdivision.middle_indices_unique source drawing 1

theorem subdivisionGraph_wellFormed {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    (wellFormed : source.IsWellFormed) (drawing : PeriodicGridDrawing) :
    (subdivisionGraph source drawing).IsWellFormed :=
  PeriodicGraph.BendSubdivision.wellFormed wellFormed (middle drawing)
    (fun edge _ _ member => middle_only_bends drawing edge member) (middle_indices_unique source drawing)

theorem subdivisionGraph_degreeAtMost {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {bound : Nat}
    (degree : source.DegreeAtMost bound) (bendDegree : 2 ≤ bound) (drawing : PeriodicGridDrawing) :
    (subdivisionGraph source drawing).DegreeAtMost bound :=
  PeriodicGraph.BendSubdivision.degreeAtMost degree bendDegree (middle drawing)
    (fun edge _ _ member => middle_only_bends drawing edge member) (middle_indices_unique source drawing)

theorem position_middle {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) (tagged : PeriodicEdge V × Nat) {entry : Cell × Nat}
    (member : entry ∈ BendSubdivision.internalPoints drawing tagged.2) :
    position source drawing (.bend tagged.2 entry.2) = representative drawing.gridSize entry.1 := by
  simp only [position,(BendSubdivision.internalPoint_lookup member).2.2]

theorem shiftedPosition_inside {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible source)
    (vertex : Vertex V) (originalMember : ∀ v, vertex = .original v → v ∈ source.vertices) :
    (shiftedDrawing source drawing).PositionInFundamentalSquare (shiftedPosition source drawing vertex) := by
  have gridPositive : (0 : Int) < drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have bounds : 0 ≤ (position source drawing vertex).1 ∧ (position source drawing vertex).1 < drawing.gridSize ∧
      0 ≤ (position source drawing vertex).2 ∧ (position source drawing vertex).2 < drawing.gridSize := by
    cases vertex with
    | original v =>
        have bounds := compatible.2.2.2.2.1 _ (compatible.vertexPosition_mem (originalMember v rfl))
        exact ⟨bounds.1.le,bounds.2.1,bounds.2.2.1.le,bounds.2.2.2⟩
    | bend edgeIndex pointIndex => exact representative_bounds gridPositive _
  simp only [PositionInFundamentalSquare,shiftedDrawing_gridSize,shiftedPosition,Cell.add,Cell.scale,Nat.cast_mul,Nat.cast_ofNat]
  omega

theorem shiftedRoute_affine {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) (edge : PeriodicEdge (Vertex V)) :
    shiftedRoute source drawing edge = (straightRoute source drawing edge).map
      (fun point => Cell.add (1,1) (Cell.scale 2 point)) := by
  simp only [shiftedRoute,straightRoute,shiftedPosition,List.map_cons,List.map_nil,Cell.scale_add,Cell.scale_scale]
  congr 2
  apply Prod.ext <;> dsimp [Cell.add,Cell.scale] <;> ring

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
