/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingCutPieceParameterPoints

/-! # Crossing-piece endpoints have matching old and new cut coordinates -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement

theorem crossingEdgePiece_endpoint_data {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (index : Nat) (line : Int)
    (nonvertical : (drawing.liftedStraightSegment index (0,0)).start.1 ≠
      (drawing.liftedStraightSegment index (0,0)).finish.1) (exit : Bool) :
    let right := if (drawing.liftedStraightSegment index (0,0)).start.1 < (drawing.liftedStraightSegment index (0,0)).finish.1 then !exit else exit
    (if exit then (crossingEdgePiece graph drawing index line).route.getLast? else (crossingEdgePiece graph drawing index line).route.head?) =
      some ((paddedRefinementFactor drawing.gridSize : Int)*line+(if right then -5 else 5)*crossingBound drawing.gridSize,
        paddedPeriodicColumnHeight graph drawing line ((drawing.liftedStraightSegment index (0,0)).rationalLineHeight line)) ∧
    ((drawing.liftedStraightSegment index (0,0)).rationalPointAtParameter
      (if exit then (crossingEdgePiece graph drawing index line).finish else (crossingEdgePiece graph drawing index line).start)).1 =
      (line : ℚ)+(if right then -columnPerturbation graph drawing else columnPerturbation graph drawing) := by
  have old := crossingEdgePiece_endpoint_original_x planar straight index line nonvertical
  dsimp only
  constructor
  · cases exit <;> by_cases forward : (drawing.liftedStraightSegment index (0,0)).start.1 < (drawing.liftedStraightSegment index (0,0)).finish.1
    all_goals simp [forward,crossingEdgePiece,paddedCrossingRoute,enlargedCrossingBar,sub_eq_add_neg]
  · cases exit <;> by_cases forward : (drawing.liftedStraightSegment index (0,0)).start.1 < (drawing.liftedStraightSegment index (0,0)).finish.1
    · simpa [forward] using old.1
    · simpa [forward] using old.1
    · simpa [forward] using old.2
    · simpa [forward] using old.2

end LeanTrominoes.PeriodicGridDrawing
