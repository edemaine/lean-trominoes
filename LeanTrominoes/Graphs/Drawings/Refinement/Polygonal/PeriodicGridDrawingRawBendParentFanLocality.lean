/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingRawBendParentBoundarySigns
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingRawBendFanRectangleLocality
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingRawBendPeriodicCores

/-! # Actual inserted-bend fans stay inside their scaled parent rectangles -/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem bend_fanRoute_inside_parent_rectangle {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (drawingLocal : drawing.IsRealLocal source)
    {parent : PeriodicEdge V × Nat} (parentMember : parent ∈ source.edges.zipIdx)
    {port : GraphPort (Vertex V)} (portMember : port ∈ allPorts (subdivisionGraph source drawing))
    {edgeIndex pointIndex : Nat} (parentIndex : parent.2 = edgeIndex) (vertex : port.vertex = .bend edgeIndex pointIndex)
    {point : Cell} (member : point ∈ fanRoute source drawing port) :
    (Cubic.coreFactor drawing.gridSize : Int)*min 0 ((drawing.gridSize : Int)*parent.1.offset.1) ≤
        (Cubic.coreFactor drawing.gridSize : Int)*(bendCenter source drawing edgeIndex pointIndex).1+point.1 ∧
      (Cubic.coreFactor drawing.gridSize : Int)*(bendCenter source drawing edgeIndex pointIndex).1+point.1 ≤
        (Cubic.coreFactor drawing.gridSize : Int)*((drawing.gridSize : Int)+max 0 ((drawing.gridSize : Int)*parent.1.offset.1)) ∧
      (Cubic.coreFactor drawing.gridSize : Int)*min 0 ((drawing.gridSize : Int)*parent.1.offset.2) ≤
        (Cubic.coreFactor drawing.gridSize : Int)*(bendCenter source drawing edgeIndex pointIndex).2+point.2 ∧
      (Cubic.coreFactor drawing.gridSize : Int)*(bendCenter source drawing edgeIndex pointIndex).2+point.2 ≤
        (Cubic.coreFactor drawing.gridSize : Int)*((drawing.gridSize : Int)+max 0 ((drawing.gridSize : Int)*parent.1.offset.2)) := by
  have vertexMember := port_vertex_mem (subdivisionGraph_wellFormed planar.1.1.1 drawing) portMember
  rw [vertex] at vertexMember
  have inside := bendCenter_inside_parent_rectangle planar drawingLocal parentMember parentIndex vertexMember
  apply fanRoute_inside_rectangle planar portMember
    (by have spacing := Cubic.coreFactor_slope_spacing drawing.gridSize; omega) inside
  · intro value original
    rw [vertex] at original
    cases original
  · intro boundary other otherMember
    have data : other ∈ allPorts (subdivisionGraph source drawing) ∧ other.vertex = .bend edgeIndex pointIndex := by
      simpa only [portsAt,List.mem_filter,decide_eq_true_eq,vertex] using otherMember
    exact (bend_port_parent_boundary_signs planar drawingLocal parentMember data.1 parentIndex data.2).1 boundary
  · intro boundary other otherMember
    have data : other ∈ allPorts (subdivisionGraph source drawing) ∧ other.vertex = .bend edgeIndex pointIndex := by
      simpa only [portsAt,List.mem_filter,decide_eq_true_eq,vertex] using otherMember
    exact (bend_port_parent_boundary_signs planar drawingLocal parentMember data.1 parentIndex data.2).2.1 boundary
  · intro boundary other otherMember
    have data : other ∈ allPorts (subdivisionGraph source drawing) ∧ other.vertex = .bend edgeIndex pointIndex := by
      simpa only [portsAt,List.mem_filter,decide_eq_true_eq,vertex] using otherMember
    exact (bend_port_parent_boundary_signs planar drawingLocal parentMember data.1 parentIndex data.2).2.2.1 boundary
  · intro boundary other otherMember
    have data : other ∈ allPorts (subdivisionGraph source drawing) ∧ other.vertex = .bend edgeIndex pointIndex := by
      simpa only [portsAt,List.mem_filter,decide_eq_true_eq,vertex] using otherMember
    exact (bend_port_parent_boundary_signs planar drawingLocal parentMember data.1 parentIndex data.2).2.2.2 boundary
  · exact member

theorem bend_fanAt_inside_parent_rectangle {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (drawingLocal : drawing.IsRealLocal source)
    {parent : PeriodicEdge V × Nat} (parentMember : parent ∈ source.edges.zipIdx)
    {port : GraphPort (Vertex V)} (portMember : port ∈ allPorts (subdivisionGraph source drawing))
    {edgeIndex pointIndex : Nat} (parentIndex : parent.2 = edgeIndex) (vertex : port.vertex = .bend edgeIndex pointIndex)
    {point : ℝ × ℝ} (contains : GridPolyline.RealContains (fanAt source drawing (Cubic.coreFactor drawing.gridSize)
      (Cubic.rasterFactor drawing.gridSize) (bendCenter source drawing edgeIndex pointIndex) port) point) :
    (cubicScale drawing : ℝ)*(min 0 ((drawing.gridSize : Int)*parent.1.offset.1) : Int) ≤ point.1 ∧
      point.1 ≤ (cubicScale drawing : ℝ)*((drawing.gridSize : Int)+max 0 ((drawing.gridSize : Int)*parent.1.offset.1) : Int) ∧
      (cubicScale drawing : ℝ)*(min 0 ((drawing.gridSize : Int)*parent.1.offset.2) : Int) ≤ point.2 ∧
      point.2 ≤ (cubicScale drawing : ℝ)*((drawing.gridSize : Int)+max 0 ((drawing.gridSize : Int)*parent.1.offset.2) : Int) := by
  have bounds := fanAt_real_inside_rectangle (Cubic.rasterFactor drawing.gridSize)
    (fun point member => bend_fanRoute_inside_parent_rectangle planar drawingLocal parentMember portMember parentIndex vertex member) contains
  simpa only [cubicScale,Int.cast_mul,Int.cast_natCast] using bounds

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
