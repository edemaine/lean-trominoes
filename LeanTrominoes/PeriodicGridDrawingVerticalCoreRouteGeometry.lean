/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingVerticalFanRoute
import LeanTrominoes.GridSegmentVerticalCore
import LeanTrominoes.GridPolylineRealOpenSimple

/-! # The shortened vertical core is simple, orthogonal, and inside its old segment -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem verticalCoreRoute_eq_segment {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (vertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 =
      (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1) :
    let core := (drawing.straightSegment tagged.2).verticalCore (paddedRefinementFactor drawing.gridSize) (crossingBound drawing.gridSize)
    verticalCoreRoute graph drawing tagged = [core.start,core.finish] :=
  verticalCoreRoute_coordinates planar degree straight member vertical

theorem verticalCoreRoute_valid {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (vertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 =
      (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1) :
    GridPolyline.IsRealOpenSimple (verticalCoreRoute graph drawing tagged) ∧
      OrthogonalPolyline (verticalCoreRoute graph drawing tagged) ∧
      ∀ point, GridPolyline.RealContains (verticalCoreRoute graph drawing tagged) point →
        ((drawing.straightSegment tagged.2).scale (paddedRefinementFactor drawing.gridSize)).RealContains point := by
  have oldX : (drawing.straightSegment tagged.2).start.1 = (drawing.straightSegment tagged.2).finish.1 := by
    simpa [liftedStraightSegment,GridSegment.translate,Cell.add] using vertical
  have nondegenerate := straightSegment_nondegenerate planar.1 member (straight _ member)
  have oldVertical : (drawing.straightSegment tagged.2).IsVertical :=
    ⟨oldX,fun same => nondegenerate (Prod.ext oldX same)⟩
  have spacing : 20*(crossingBound drawing.gridSize : Int) < paddedRefinementFactor drawing.gridSize := by
    simp only [paddedRefinementFactor,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
    have nonnegative : (0 : Int) ≤ crossingBound drawing.gridSize := by positivity
    omega
  let core := (drawing.straightSegment tagged.2).verticalCore (paddedRefinementFactor drawing.gridSize) (crossingBound drawing.gridSize)
  have coreVertical : core.IsVertical := GridSegment.verticalCore_isVertical oldVertical spacing
  have unequal : core.start ≠ core.finish := fun equal => coreVertical.2 (congrArg Prod.snd equal)
  rw [verticalCoreRoute_eq_segment planar degree straight member vertical]
  refine ⟨?_,?_,?_⟩
  · apply GridPolyline.isRealOpenSimple_of_box_certificate
    simpa [GridPolyline.SimpleBoxCertificate,gridPolylineSegments] using unequal
  · simp only [OrthogonalPolyline,List.isChain_cons_cons,List.isChain_singleton,and_true]
    exact Or.inr coreVertical
  · intro point contains
    have coreContains : core.RealContains point := by
      simpa [GridPolyline.RealContains,gridPolylineSegments] using contains
    exact GridSegment.verticalCore_realContains_parent oldVertical spacing coreContains

theorem verticalFanRouteWord_connected {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (tagged : PeriodicEdge Vertex × Nat) :
    (verticalFanRouteWord graph drawing tagged).IsChain (fun first last => first.getLast? = last.head?) := by
  have sourceLong := (paddedIncidenceRoute_isRealOpenSimple graph drawing (sourcePort tagged.1 tagged.2)).1
  have targetLong := (liftedPaddedIncidenceRoute_isRealOpenSimple graph drawing (targetPort tagged.1 tagged.2) tagged.1.offset).1
  have sourceSome : (paddedIncidenceRoute graph drawing (sourcePort tagged.1 tagged.2)).getLast? =
      some ((paddedIncidenceRoute graph drawing (sourcePort tagged.1 tagged.2)).getLast?.getD (0,0)) := by
    cases last : (paddedIncidenceRoute graph drawing (sourcePort tagged.1 tagged.2)).getLast? with
    | none => have empty := List.getLast?_eq_none_iff.mp last; simp [empty] at sourceLong
    | some point => simp
  have targetSome : (liftedPaddedIncidenceRoute graph drawing (targetPort tagged.1 tagged.2) tagged.1.offset).getLast? =
      some ((liftedPaddedIncidenceRoute graph drawing (targetPort tagged.1 tagged.2) tagged.1.offset).getLast?.getD (0,0)) := by
    cases last : (liftedPaddedIncidenceRoute graph drawing (targetPort tagged.1 tagged.2) tagged.1.offset).getLast? with
    | none => have empty := List.getLast?_eq_none_iff.mp last; simp [empty] at targetLong
    | some point => simp
  apply List.isChain_cons_cons.mpr
  refine ⟨sourceSome,?_⟩
  apply List.isChain_cons_cons.mpr
  refine ⟨?_,by simp only [List.isChain_singleton]⟩
  simpa only [verticalCoreRoute,List.getLast?_cons_cons,List.getLast?_singleton,List.head?_reverse] using targetSome.symm

end LeanTrominoes.PeriodicGridDrawing
