/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingEdgePieceEnumeration
import LeanTrominoes.PeriodicGridDrawingCrossingPieceWindow
import LeanTrominoes.PeriodicGridDrawingPaddedCrossingSeparation

/-! # Crossing bars and endpoint fans of a nonvertical edge are geometrically separate -/
namespace LeanTrominoes.PeriodicGridDrawing
open PeriodicOrthocrossing OrthogonalDrawingRefinement

theorem crossingEdgePiece_raw_image {Vertex : Type*}
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (index : Nat) (line : Int) (point : ℝ × ℝ) :
    GridPolyline.RealContains (crossingEdgePiece graph drawing index line).route point ↔
      GridPolyline.RealContains (paddedCrossingRoute graph drawing line (index,(0,0))) point := by
  unfold crossingEdgePiece
  dsimp only
  split_ifs
  · rfl
  · exact GridPolyline.realContains_reverse _ _

theorem sourceEdgePiece_lifted_image {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (tagged : PeriodicEdge Vertex × Nat) (point : ℝ × ℝ) :
    GridPolyline.RealContains (sourceEdgePiece graph drawing tagged).route point ↔
      GridPolyline.RealContains (liftedPaddedIncidenceRoute graph drawing (sourcePort tagged.1 tagged.2) (0,0)) point := by
  rw [liftedPaddedIncidenceRoute_eq_translate]
  simp [sourceEdgePiece,Cell.scale,translatePolyline_zero]

theorem crossingEdgePiece_avoids_endpoint_fans {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (compatible : drawing.IsCompatible graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (straight : (drawing.edgeRoute tagged.2).length = 2) (line : Int)
    (crosses : (drawing.liftedStraightSegment tagged.2 (0,0)).CrossesVerticalLine line) {point : ℝ × ℝ}
    (barContains : GridPolyline.RealContains (crossingEdgePiece graph drawing tagged.2 line).route point) :
    ¬GridPolyline.RealContains (sourceEdgePiece graph drawing tagged).route point ∧
      ¬GridPolyline.RealContains (targetEdgePiece graph drawing tagged).route point := by
  have crossing := periodic_crossing_residue_mem compatible member straight
    (graphLocal _ (List.fst_mem_of_mem_zipIdx member)) (0,0) crosses
  have raw := (crossingEdgePiece_raw_image graph drawing tagged.2 line point).mp barContains
  constructor
  · intro contains
    exact paddedCrossingBar_avoids_incidence_route compatible degree crossing (sourcePort_mem_allPorts graph member) (0,0) raw
      ((sourceEdgePiece_lifted_image graph drawing tagged point).mp contains)
  · intro contains
    change GridPolyline.RealContains (liftedPaddedIncidenceRoute graph drawing (targetPort tagged.1 tagged.2) tagged.1.offset).reverse point at contains
    exact paddedCrossingBar_avoids_incidence_route compatible degree crossing (targetPort_mem_allPorts graph member) tagged.1.offset raw
      ((GridPolyline.realContains_reverse _ _).mp contains)

theorem source_target_pieces_disjoint {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (nonvertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 ≠
      (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1) {point : ℝ × ℝ}
    (sourceContains : GridPolyline.RealContains (sourceEdgePiece graph drawing tagged).route point)
    (targetContains : GridPolyline.RealContains (targetEdgePiece graph drawing tagged).route point) : False := by
  have sourceRaw := (sourceEdgePiece_lifted_image graph drawing tagged point).mp sourceContains
  have targetRaw : GridPolyline.RealContains (liftedPaddedIncidenceRoute graph drawing (targetPort tagged.1 tagged.2) tagged.1.offset) point :=
    (GridPolyline.realContains_reverse _ _).mp targetContains
  have contact := liftedPaddedIncidenceRoutes_contact planar.1.1
    (distinctPortRayKeys_of_planar_straight planar straight) degree
    (sourcePort_mem_allPorts graph member) (targetPort_mem_allPorts graph member) (0,0) tagged.1.offset sourceRaw targetRaw
  have vertices : tagged.1.source = tagged.1.target := contact.1
  have offset : tagged.1.offset = (0,0) := contact.2.1.symm
  apply nonvertical
  rw [liftedStraightSegment_start planar.1.1 member,liftedStraightSegment_finish planar.1.1 member,vertices,offset]
  simp [Cell.add]

theorem crossingEdgePieces_contact_same_line {Vertex : Type*}
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (index : Nat) (firstLine lastLine : Int)
    {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains (crossingEdgePiece graph drawing index firstLine).route point)
    (lastContains : GridPolyline.RealContains (crossingEdgePiece graph drawing index lastLine).route point) : firstLine = lastLine := by
  have spacing : 10*(crossingBound drawing.gridSize : Int) < paddedRefinementFactor drawing.gridSize := by
    simp only [paddedRefinementFactor,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
    have nonnegative : (0 : Int) ≤ crossingBound drawing.gridSize := by positivity
    omega
  exact (enlargedCrossingBars_contact_same_column spacing
    ((crossingEdgePiece_raw_image graph drawing index firstLine point).mp firstContains)
    ((crossingEdgePiece_raw_image graph drawing index lastLine point).mp lastContains)).1

theorem cutPieces_contact_eq {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (nonvertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 ≠
      (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1) {first last : EdgeRoutePiece}
    (firstMember : first = sourceEdgePiece graph drawing tagged ∨
      first ∈ crossingEdgePieces graph drawing tagged.2 ∨ first = targetEdgePiece graph drawing tagged)
    (lastMember : last = sourceEdgePiece graph drawing tagged ∨
      last ∈ crossingEdgePieces graph drawing tagged.2 ∨ last = targetEdgePiece graph drawing tagged)
    {point : ℝ × ℝ} (firstContains : GridPolyline.RealContains first.route point)
    (lastContains : GridPolyline.RealContains last.route point) : first = last := by
  rcases firstMember with source | crossing | target
  · subst first
    rcases lastMember with source | crossing | target
    · exact source.symm
    · obtain ⟨line,_,lookup⟩ := List.mem_filterMap.mp crossing
      split_ifs at lookup with crosses
      have equal := Option.some.inj lookup
      subst last
      exact ((crossingEdgePiece_avoids_endpoint_fans planar.1.1 degree graphLocal member (straight _ member) line crosses lastContains).1 firstContains).elim
    · subst last
      exact (source_target_pieces_disjoint planar degree straight member nonvertical firstContains lastContains).elim
  · obtain ⟨firstLine,_,lookup⟩ := List.mem_filterMap.mp crossing
    split_ifs at lookup with firstCrosses
    have equal := Option.some.inj lookup
    subst first
    rcases lastMember with source | crossing | target
    · subst last
      exact ((crossingEdgePiece_avoids_endpoint_fans planar.1.1 degree graphLocal member (straight _ member) firstLine firstCrosses firstContains).1 lastContains).elim
    · obtain ⟨lastLine,_,lookup⟩ := List.mem_filterMap.mp crossing
      split_ifs at lookup with lastCrosses
      have equal := Option.some.inj lookup
      subst last
      exact congrArg (crossingEdgePiece graph drawing tagged.2)
        (crossingEdgePieces_contact_same_line graph drawing tagged.2 firstLine lastLine firstContains lastContains)
    · subst last
      exact ((crossingEdgePiece_avoids_endpoint_fans planar.1.1 degree graphLocal member (straight _ member) firstLine firstCrosses firstContains).2 lastContains).elim
  · subst first
    rcases lastMember with source | crossing | target
    · subst last
      exact (source_target_pieces_disjoint planar degree straight member nonvertical lastContains firstContains).elim
    · obtain ⟨line,_,lookup⟩ := List.mem_filterMap.mp crossing
      split_ifs at lookup with crosses
      have equal := Option.some.inj lookup
      subst last
      exact ((crossingEdgePiece_avoids_endpoint_fans planar.1.1 degree graphLocal member (straight _ member) line crosses lastContains).2 firstContains).elim
    · exact target.symm

end LeanTrominoes.PeriodicGridDrawing
