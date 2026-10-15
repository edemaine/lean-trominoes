/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.General.PeriodicOrthocrossingGeneralCoreEndpointColumns

/-! # An active vertical column cannot pass through another edge's bend -/
namespace LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
attribute [local irreducible] classifiedCore core

theorem private_column_contact_index {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} (wellFormed : graph.IsWellFormed)
    {verticalTagged columnTagged : PeriodicEdge Vertex × Nat}
    (verticalEdgeMember : verticalTagged ∈ graph.edges.zipIdx) (columnEdgeMember : columnTagged ∈ graph.edges.zipIdx)
    {piece : ClassifiedSegment Vertex} (pieceMember : piece ∈ classifiedCore graph verticalTagged.1 verticalTagged.2)
    (active : piece.role.IsActiveVertical) (vertical : piece.segment.IsVertical)
    {x firstShift secondShift : Int} (column : CoreColumn graph columnTagged.1 columnTagged.2 x)
    (equal : verticalBase graph piece.role+(drawingGridSize graph : Int)*firstShift =
      x+(drawingGridSize graph : Int)*secondShift) : verticalTagged.2 = columnTagged.2 := by
  have pieceBounds := classifiedCore_vertical_base_bounds wellFormed verticalEdgeMember piece pieceMember vertical
  have pieceEnd := classifiedCore_activeEnd_correct graph verticalTagged.1 verticalTagged.2 piece pieceMember
  have piecePorts := classifiedCore_activePort_mem verticalEdgeMember piece pieceMember
  have gridPositive : (0 : Int) < drawingGridSize graph := by exact_mod_cast drawingGridSize_pos graph
  have identify (expected : SegmentRole Vertex) (expectedActive : expected.IsActiveVertical)
      (expectedEnd : expected.ActiveVerticalEndCorrect)
      (expectedPorts : ∀ port, expected.activeVerticalPort = some port → port ∈ allPorts graph)
      (expectedIndex : expected.edgeIndex = columnTagged.2)
      (baseEqual : verticalBase graph piece.role = verticalBase graph expected) :
      verticalTagged.2 = columnTagged.2 := by
    have roles := active_vertical_roles_eq_of_bases_eq wellFormed active expectedActive
      pieceEnd expectedEnd piecePorts expectedPorts baseEqual
    have indices := congrArg SegmentRole.edgeIndex roles
    rw [classifiedCore_role_index graph verticalTagged.1 verticalTagged.2 piece pieceMember,expectedIndex] at indices
    exact indices
  obtain ⟨shift,sourceColumn | targetColumn | gateColumn | boundaryColumn⟩ := column
  · rw [sourceColumn] at equal
    have normalized : verticalBase graph piece.role+(drawingGridSize graph : Int)*firstShift =
        portX graph (sourcePort columnTagged.1 columnTagged.2)+(drawingGridSize graph : Int)*(shift+secondShift) := by
      linear_combination equal
    have ports := sourcePort_mem_allPorts graph columnEdgeMember
    have bounds := portX_lt_gridSize wellFormed ports
    have lanes := periodic_coordinate_unique gridPositive pieceBounds (by omega :
      0 ≤ portX graph (sourcePort columnTagged.1 columnTagged.2) ∧
        portX graph (sourcePort columnTagged.1 columnTagged.2) < drawingGridSize graph) normalized
    apply identify (.sourcePortVertical (sourcePort columnTagged.1 columnTagged.2)) (by trivial)
      (by simp [SegmentRole.ActiveVerticalEndCorrect,sourcePort])
      (by simpa [SegmentRole.activeVerticalPort] using ports) (by rfl) lanes.1
  · rw [targetColumn] at equal
    have normalized : verticalBase graph piece.role+(drawingGridSize graph : Int)*firstShift =
        portX graph (targetPort columnTagged.1 columnTagged.2)+(drawingGridSize graph : Int)*(shift+secondShift) := by
      linear_combination equal
    have ports := targetPort_mem_allPorts graph columnEdgeMember
    have bounds := portX_lt_gridSize wellFormed ports
    have lanes := periodic_coordinate_unique gridPositive pieceBounds (by omega :
      0 ≤ portX graph (targetPort columnTagged.1 columnTagged.2) ∧
        portX graph (targetPort columnTagged.1 columnTagged.2) < drawingGridSize graph) normalized
    apply identify (.targetPortVertical (targetPort columnTagged.1 columnTagged.2)) (by trivial)
      (by simp [SegmentRole.ActiveVerticalEndCorrect,targetPort])
      (by simpa [SegmentRole.activeVerticalPort] using ports) (by rfl) lanes.1
  · rw [gateColumn] at equal
    have normalized : verticalBase graph piece.role+(drawingGridSize graph : Int)*firstShift =
        gateX graph columnTagged.2+(drawingGridSize graph : Int)*(shift+secondShift) := by linear_combination equal
    have valid : columnTagged.2 < graph.edges.length := List.snd_lt_of_mem_zipIdx columnEdgeMember
    have gateBounds : 0 ≤ gateX graph columnTagged.2 ∧ gateX graph columnTagged.2 < drawingGridSize graph := by
      unfold gateX drawingGridSize
      omega
    have lanes := periodic_coordinate_unique gridPositive pieceBounds gateBounds normalized
    apply identify (.gateVertical columnTagged.2) (by trivial) (by trivial)
      (by simp [SegmentRole.activeVerticalPort]) (by rfl) lanes.1
  · rw [boundaryColumn] at equal
    have normalized : verticalBase graph piece.role+(drawingGridSize graph : Int)*firstShift =
        0+(drawingGridSize graph : Int)*(shift+secondShift) := by linear_combination equal
    have lanes := periodic_coordinate_unique gridPositive pieceBounds (by omega : (0 : Int) ≤ 0 ∧ (0 : Int) < drawingGridSize graph) normalized
    have positive := classifiedCore_active_base_positive wellFormed verticalEdgeMember pieceMember active
    omega

theorem vertical_endpoint_contact_index {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} (wellFormed : graph.IsWellFormed)
    {verticalTagged columnTagged : PeriodicEdge Vertex × Nat}
    (verticalEdgeMember : verticalTagged ∈ graph.edges.zipIdx) (columnEdgeMember : columnTagged ∈ graph.edges.zipIdx)
    (edgeLocal : verticalTagged.1.span ≤ 1)
    {piece : ClassifiedSegment Vertex} (pieceMember : piece ∈ classifiedCore graph verticalTagged.1 verticalTagged.2)
    (active : piece.role.IsActiveVertical) (vertical : piece.segment.IsVertical) {endpoint : Cell}
    (column : CoreColumn graph columnTagged.1 columnTagged.2 endpoint.1) (firstCell secondCell : Cell)
    (contains : (piece.segment.translate (Cell.scale (drawingGridSize graph : Int) firstCell)).RealContains
      (realCell (Cell.add (Cell.scale (drawingGridSize graph : Int) secondCell) endpoint))) :
    verticalTagged.2 = columnTagged.2 := by
  have fixed := GridSegment.realContains_vertical_x ((GridSegment.isVertical_translate _ _).mpr vertical) contains
  change ((Cell.add (Cell.scale (drawingGridSize graph : Int) secondCell) endpoint).1 : ℝ) =
    ((piece.segment.translate (Cell.scale (drawingGridSize graph : Int) firstCell)).start.1 : ℝ) at fixed
  have fixedInt : (Cell.add (Cell.scale (drawingGridSize graph : Int) secondCell) endpoint).1 =
      (piece.segment.translate (Cell.scale (drawingGridSize graph : Int) firstCell)).start.1 := by exact_mod_cast fixed
  change (drawingGridSize graph : Int)*secondCell.1+endpoint.1 =
    (drawingGridSize graph : Int)*firstCell.1+piece.segment.start.1 at fixedInt
  rw [classifiedCore_vertical_column graph verticalTagged.1 verticalTagged.2 edgeLocal piece pieceMember vertical] at fixedInt
  apply private_column_contact_index wellFormed verticalEdgeMember columnEdgeMember pieceMember active vertical column
    (firstShift := verticalShift verticalTagged.1 piece.role+firstCell.1) (secondShift := secondCell.1)
  linear_combination -fixedInt

end LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
