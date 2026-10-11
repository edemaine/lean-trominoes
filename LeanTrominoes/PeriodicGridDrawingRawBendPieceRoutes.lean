/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendDigitalCores
import LeanTrominoes.PeriodicGridDrawingRawBendFanPlacement

/-! # Assembling the fan, digital core, and reversed fan of each raw piece

The assembled routes are orthogonal and have exactly scaled raw endpoints.
Their closed images split into their three advertised components. Global
contact and parent-route locality proofs are separate obligations.
-/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement PeriodicOrthocrossing

def pieceSourceFan {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge (Vertex V) × Nat) : List Cell :=
  fanAt source drawing (Cubic.coreFactor drawing.gridSize) (Cubic.rasterFactor drawing.gridSize)
    (subdivisionSegment source drawing tagged.1).start (sourcePort tagged.1 tagged.2)

def pieceTargetFan {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge (Vertex V) × Nat) : List Cell :=
  (fanAt source drawing (Cubic.coreFactor drawing.gridSize) (Cubic.rasterFactor drawing.gridSize)
    (subdivisionSegment source drawing tagged.1).finish (targetPort tagged.1 tagged.2)).reverse

noncomputable def pieceRoute {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge (Vertex V) × Nat) : List Cell :=
  joinAtEndpoint (joinAtEndpoint (pieceSourceFan source drawing tagged) (coreRoute source drawing tagged))
    (pieceTargetFan source drawing tagged)

theorem pieceSourceFan_head {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge (Vertex V) × Nat) :
    (pieceSourceFan source drawing tagged).head? = some (Cell.scale
      ((Cubic.rasterFactor drawing.gridSize : Int)*(Cubic.coreFactor drawing.gridSize : Int))
      (subdivisionSegment source drawing tagged.1).start) := fanAt_head _ _ _ _ _ _

theorem pieceTargetFan_last {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge (Vertex V) × Nat) :
    (pieceTargetFan source drawing tagged).getLast? = some (Cell.scale
      ((Cubic.rasterFactor drawing.gridSize : Int)*(Cubic.coreFactor drawing.gridSize : Int))
      (subdivisionSegment source drawing tagged.1).finish) := by
  rw [pieceTargetFan,List.getLast?_reverse]
  exact fanAt_head _ _ _ _ _ _

theorem pieceSourceFan_last {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge (Vertex V) × Nat) :
    (pieceSourceFan source drawing tagged).getLast? = some (cubicCore source drawing tagged).start := by
  rw [pieceSourceFan,fanAt_last]
  congr 1
  apply Prod.ext <;> simp only [cubicCore,anchoredSegment,GridSegment.scale,Cell.add,Cell.scale] <;> ring

theorem pieceTargetFan_head {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge (Vertex V) × Nat) :
    (pieceTargetFan source drawing tagged).head? = some (cubicCore source drawing tagged).finish := by
  rw [pieceTargetFan,List.head?_reverse,fanAt_last]
  congr 1
  apply Prod.ext <;> simp only [cubicCore,anchoredSegment,GridSegment.scale,Cell.add,Cell.scale] <;> ring

theorem pieceRoute_endpoints {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge (Vertex V) × Nat) :
    (pieceRoute source drawing tagged).head? = some (Cell.scale
      ((Cubic.rasterFactor drawing.gridSize : Int)*(Cubic.coreFactor drawing.gridSize : Int))
      (subdivisionSegment source drawing tagged.1).start) ∧
    (pieceRoute source drawing tagged).getLast? = some (Cell.scale
      ((Cubic.rasterFactor drawing.gridSize : Int)*(Cubic.coreFactor drawing.gridSize : Int))
      (subdivisionSegment source drawing tagged.1).finish) := by
  exact ⟨joinAtEndpoint_head? (joinAtEndpoint_head? (pieceSourceFan_head source drawing tagged)),
    joinAtEndpoint_getLast?
      (joinAtEndpoint_getLast? (pieceSourceFan_last source drawing tagged) (coreRoute_endpoints source drawing tagged).1
        (coreRoute_endpoints source drawing tagged).2)
      (pieceTargetFan_head source drawing tagged) (pieceTargetFan_last source drawing tagged)⟩

theorem pieceRoute_orthogonal {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) {tagged : PeriodicEdge (Vertex V) × Nat}
    (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx) : OrthogonalPolyline (pieceRoute source drawing tagged) := by
  have first := fanAt_orthogonal planar (Cubic.coreFactor drawing.gridSize)
    (Cubic.rasterFactor_positive drawing.gridSize) (subdivisionSegment source drawing tagged.1).start
    (sourcePort_mem_allPorts _ member)
  have last := (fanAt_orthogonal planar (Cubic.coreFactor drawing.gridSize)
    (Cubic.rasterFactor_positive drawing.gridSize) (subdivisionSegment source drawing tagged.1).finish
    (targetPort_mem_allPorts _ member)).reverse
  exact (first.joinAtEndpoint (coreRoute_orthogonal source drawing tagged)
    (pieceSourceFan_last source drawing tagged) (coreRoute_endpoints source drawing tagged).1).joinAtEndpoint last
    (joinAtEndpoint_getLast? (pieceSourceFan_last source drawing tagged) (coreRoute_endpoints source drawing tagged).1
      (coreRoute_endpoints source drawing tagged).2) (pieceTargetFan_head source drawing tagged)

theorem pieceRoute_contains (V : Type*) [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge (Vertex V) × Nat) (point : ℝ × ℝ) :
    GridPolyline.RealContains (pieceRoute source drawing tagged) point ↔
      GridPolyline.RealContains (pieceSourceFan source drawing tagged) point ∨
      GridPolyline.RealContains (coreRoute source drawing tagged) point ∨
      GridPolyline.RealContains (pieceTargetFan source drawing tagged) point := by
  have joint : (joinPolylines (pieceSourceFan source drawing tagged) (coreRoute source drawing tagged)).getLast? =
      some (cubicCore source drawing tagged).finish :=
    joinAtEndpoint_getLast? (pieceSourceFan_last source drawing tagged) (coreRoute_endpoints source drawing tagged).1
      (coreRoute_endpoints source drawing tagged).2
  change GridPolyline.RealContains
    (joinPolylines (joinPolylines (pieceSourceFan source drawing tagged) (coreRoute source drawing tagged))
      (pieceTargetFan source drawing tagged)) point ↔ _
  rw [GridPolyline.realContains_join joint (pieceTargetFan_head source drawing tagged),
    GridPolyline.realContains_join (pieceSourceFan_last source drawing tagged) (coreRoute_endpoints source drawing tagged).1]
  exact or_assoc

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
