/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendDigitalCores
import LeanTrominoes.GridSegmentRealTubeTranslation

/-! # Tube bounds and nonincident core separation in all periodic copies -/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement PeriodicOrthocrossing

def cubicScale (drawing : PeriodicGridDrawing) : Int :=
  (Cubic.rasterFactor drawing.gridSize : Int)*(Cubic.coreFactor drawing.gridSize : Int)

noncomputable def liftedCoreRoute {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge (Vertex V) × Nat) (copy : Cell) : List Cell :=
  translatePolyline (Cell.scale (cubicScale drawing*drawing.gridSize) copy) (coreRoute source drawing tagged)

theorem liftedCoreRoute_tube {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge (Vertex V) × Nat) (copy : Cell) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (liftedCoreRoute source drawing tagged copy) point) :
    (((subdivisionSegment source drawing tagged.1).translate (drawing.periodTranslation copy)).scale (cubicScale drawing)).RealTubeContains
      ((Cubic.rasterFactor drawing.gridSize : ℝ)*10+3) point := by
  have original := (GridPolyline.realContains_translate_inverse _ _ _).mp contains
  have tube := coreRoute_tube source drawing tagged original
  have shifted := tube.translate_scaled (drawing.periodTranslation copy)
  have x : (cubicScale drawing : ℝ)*(drawing.periodTranslation copy).1+
      (point.1-(Cell.scale (cubicScale drawing*drawing.gridSize) copy).1) = point.1 := by
    simp only [periodTranslation,Cell.scale,Int.cast_mul]
    ring
  have y : (cubicScale drawing : ℝ)*(drawing.periodTranslation copy).2+
      (point.2-(Cell.scale (cubicScale drawing*drawing.gridSize) copy).2) = point.2 := by
    simp only [periodTranslation,Cell.scale,Int.cast_mul]
    ring
  change (((subdivisionSegment source drawing tagged.1).translate (drawing.periodTranslation copy)).scale (cubicScale drawing)).RealTubeContains
    ((Cubic.rasterFactor drawing.gridSize : ℝ)*10+3)
    ((cubicScale drawing : ℝ)*(drawing.periodTranslation copy).1+
      (point.1-(Cell.scale (cubicScale drawing*drawing.gridSize) copy).1),
      (cubicScale drawing : ℝ)*(drawing.periodTranslation copy).2+
      (point.2-(Cell.scale (cubicScale drawing*drawing.gridSize) copy).2)) at shifted
  simpa only [x,y,Prod.mk.eta] using shifted

theorem cubicScale_tube_spacing (drawing : PeriodicGridDrawing) :
    4*(2*(drawing.gridSize : ℝ))*((Cubic.rasterFactor drawing.gridSize : ℝ)*10+3) < (cubicScale drawing : ℝ) := by
  have rasterPositive : (0 : Int) < Cubic.rasterFactor drawing.gridSize := by
    exact_mod_cast Cubic.rasterFactor_positive drawing.gridSize
  have realRasterPositive : (0 : ℝ) < Cubic.rasterFactor drawing.gridSize := by exact_mod_cast rasterPositive
  have rasterAtLeastOne : (1 : ℝ) ≤ Cubic.rasterFactor drawing.gridSize := by
    exact_mod_cast (show 1 ≤ (Cubic.rasterFactor drawing.gridSize : Int) by omega)
  have base : 4*(2*(drawing.gridSize : ℝ))*(10+3) < (Cubic.coreFactor drawing.gridSize : ℝ) := by
    exact_mod_cast Cubic.coreFactor_tube_spacing drawing.gridSize
  have scaled := mul_lt_mul_of_pos_left base realRasterPositive
  simp only [cubicScale,Int.cast_mul,Int.cast_natCast]
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ drawing.gridSize by positivity) (sub_nonneg.mpr rasterAtLeastOne)]

theorem liftedCoreRoutes_disjoint {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (graphLocal : source.IsLocal) (drawingLocal : drawing.IsRealLocal source)
    {first second : PeriodicEdge (Vertex V) × Nat}
    (firstMember : first ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (secondMember : second ∈ (subdivisionGraph source drawing).edges.zipIdx) (firstCopy secondCopy : Cell)
    (disjoint : ∀ point : ℝ × ℝ,
      ((subdivisionSegment source drawing first.1).translate (drawing.periodTranslation firstCopy)).RealContains point →
      ¬((subdivisionSegment source drawing second.1).translate (drawing.periodTranslation secondCopy)).RealContains point)
    {point : ℝ × ℝ} (firstContains : GridPolyline.RealContains (liftedCoreRoute source drawing first firstCopy) point) :
    ¬GridPolyline.RealContains (liftedCoreRoute source drawing second secondCopy) point := by
  intro secondContains
  have firstBounds := subdivisionSegment_direction_bounds planar.1 graphLocal drawingLocal firstMember
  have secondBounds := subdivisionSegment_direction_bounds planar.1 graphLocal drawingLocal secondMember
  have translatedFirstBounds :
      |((subdivisionSegment source drawing first.1).translate (drawing.periodTranslation firstCopy)).direction.1| ≤ 2*(drawing.gridSize : Int) ∧
      |((subdivisionSegment source drawing first.1).translate (drawing.periodTranslation firstCopy)).direction.2| ≤ 2*(drawing.gridSize : Int) := by
    simpa only [GridSegment.direction_translate] using firstBounds
  have translatedSecondBounds :
      |((subdivisionSegment source drawing second.1).translate (drawing.periodTranslation secondCopy)).direction.1| ≤ 2*(drawing.gridSize : Int) ∧
      |((subdivisionSegment source drawing second.1).translate (drawing.periodTranslation secondCopy)).direction.2| ≤ 2*(drawing.gridSize : Int) := by
    simpa only [GridSegment.direction_translate] using secondBounds
  have gridPositive : (0 : Int) < drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  exact GridSegment.scaled_tubes_disjoint (by omega) (by positivity)
    (by simpa using cubicScale_tube_spacing drawing) translatedFirstBounds translatedSecondBounds disjoint point
    (liftedCoreRoute_tube source drawing first firstCopy firstContains)
    (liftedCoreRoute_tube source drawing second secondCopy secondContains)

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
