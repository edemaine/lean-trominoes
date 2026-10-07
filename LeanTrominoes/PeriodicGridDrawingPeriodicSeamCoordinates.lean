/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingLocalSeamBounds
import LeanTrominoes.PeriodicGridDrawingPeriodicSeamCrossingTable
import LeanTrominoes.PeriodicHeightRedistribution

/-! # Seam coordinates preserve crossing order in every period -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement

def periodicSeamCoordinate {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (abscissa : ℚ) : Int :=
  periodicRedistributedHeight drawing.gridSize (paddedGridSize drawing.gridSize)
    (seamCrossingCoordinate graph drawing 0) abscissa

def periodicSeamSlab {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (abscissa : ℚ) : Int :=
  rationalSlab abscissa (seamTowardLeft graph drawing 0 (rationalResidue drawing.gridSize abscissa))

theorem periodicSeamCoordinate_translate {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (abscissa : ℚ) (shift : Int) :
    periodicSeamCoordinate graph drawing (abscissa+(drawing.gridSize : ℚ)*shift) =
      periodicSeamCoordinate graph drawing abscissa+(paddedGridSize drawing.gridSize : Int)*shift := by
  have positive : (0 : Int) < drawing.gridSize := by unfold PeriodicGridDrawing.gridSize; omega
  unfold periodicSeamCoordinate
  simpa only [Int.cast_natCast] using periodicRedistributedHeight_translate positive (paddedGridSize drawing.gridSize) _ abscissa shift

theorem periodicSeamSlab_translate {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (abscissa : ℚ) (shift : Int) :
    periodicSeamSlab graph drawing (abscissa+(drawing.gridSize : ℚ)*shift) =
      periodicSeamSlab graph drawing abscissa+(drawing.gridSize : Int)*shift := by
  have positive : (0 : Int) < drawing.gridSize := by unfold PeriodicGridDrawing.gridSize; omega
  unfold periodicSeamSlab
  rw [show abscissa+(drawing.gridSize : ℚ)*shift = abscissa+((drawing.gridSize : Int)*shift : Int) by push_cast; rfl]
  rw [show rationalResidue drawing.gridSize (abscissa+((drawing.gridSize : Int)*shift : Int)) =
    rationalResidue drawing.gridSize abscissa by simpa only [Int.cast_mul,Int.cast_natCast] using rationalResidue_translate positive abscissa shift]
  exact rationalSlab_translate _ _ _

theorem seamCrossingCoordinate_in_cell {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph) (degree : graph.DegreeAtMost 4)
    (graphLocal : graph.IsLocal) (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {abscissa : ℚ} (member : abscissa ∈ seamCrossingAbscissae graph drawing 0) :
    0 < seamCrossingCoordinate graph drawing 0 abscissa ∧
      seamCrossingCoordinate graph drawing 0 abscissa < paddedGridSize drawing.gridSize := by
  have oldBounds := seamCrossingAbscissae_interior compatible graphLocal straight member
  have slabs := rationalSlab_in_fundamental (period := drawing.gridSize) oldBounds (seamTowardLeft graph drawing 0 abscissa)
  have bounds := seamCrossingCoordinate_bounds compatible degree member
  dsimp only at bounds
  have factorPositive : (0 : Int) < paddedRefinementFactor drawing.gridSize := by exact_mod_cast paddedRefinementFactor_positive drawing.gridSize
  have lower := mul_nonneg factorPositive.le slabs.1
  have upper := mul_le_mul_of_nonneg_left (by omega : rationalSlab abscissa (seamTowardLeft graph drawing 0 abscissa)+1 ≤ drawing.gridSize) factorPositive.le
  have nonnegative : (0 : Int) ≤ crossingBound drawing.gridSize := by positivity
  simp only [paddedGridSize,Nat.cast_mul]
  constructor <;> nlinarith

theorem periodicSeamCoordinate_slab_clearance {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph) (degree : graph.DegreeAtMost 4)
    {abscissa : ℚ} (member : rationalResidue drawing.gridSize abscissa ∈ seamCrossingAbscissae graph drawing 0) :
    (paddedRefinementFactor drawing.gridSize : Int)*periodicSeamSlab graph drawing abscissa+7*crossingBound drawing.gridSize <
      periodicSeamCoordinate graph drawing abscissa ∧
    periodicSeamCoordinate graph drawing abscissa <
      (paddedRefinementFactor drawing.gridSize : Int)*(periodicSeamSlab graph drawing abscissa+1)-7*crossingBound drawing.gridSize := by
  have bounds := seamCrossingCoordinate_bounds compatible degree member
  dsimp only at bounds
  have decomposition : abscissa = rationalResidue drawing.gridSize abscissa+
      ((drawing.gridSize : Int)*rationalCell drawing.gridSize abscissa : Int) := by
    calc abscissa = (drawing.gridSize : ℚ)*rationalCell drawing.gridSize abscissa+
        rationalResidue drawing.gridSize abscissa := rationalCoordinate_decomposition _ _
         _ = _ := by push_cast; ring
  have slab : periodicSeamSlab graph drawing abscissa =
      rationalSlab (rationalResidue drawing.gridSize abscissa)
        (seamTowardLeft graph drawing 0 (rationalResidue drawing.gridSize abscissa))+
          (drawing.gridSize : Int)*rationalCell drawing.gridSize abscissa := by
    unfold periodicSeamSlab
    conv_lhs => arg 1; rw [decomposition]
    exact rationalSlab_translate _ _ _
  simp only [periodicSeamCoordinate,periodicRedistributedHeight,slab,paddedGridSize,Nat.cast_mul]
  constructor <;> nlinarith

theorem periodicSeamCoordinate_preserves_order {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph) (degree : graph.DegreeAtMost 4)
    (graphLocal : graph.IsLocal) (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {first second : ℚ} (firstMember : rationalResidue drawing.gridSize first ∈ seamCrossingAbscissae graph drawing 0)
    (secondMember : rationalResidue drawing.gridSize second ∈ seamCrossingAbscissae graph drawing 0) (ordered : first < second) :
    periodicSeamCoordinate graph drawing first < periodicSeamCoordinate graph drawing second := by
  have positive : (0 : Int) < drawing.gridSize := by unfold PeriodicGridDrawing.gridSize; omega
  have outputPositive : (0 : Int) < paddedGridSize drawing.gridSize := by
    exact_mod_cast paddedGridSize_positive (by unfold PeriodicGridDrawing.gridSize; omega : 0 < drawing.gridSize)
  exact periodicRedistributedHeight_preserves_order positive outputPositive _ _
    (seamCrossingCoordinates_strictMonoOn compatible degree 0)
    (fun _ member => seamCrossingCoordinate_in_cell compatible degree graphLocal straight member)
    firstMember secondMember ordered

end LeanTrominoes.PeriodicGridDrawing
