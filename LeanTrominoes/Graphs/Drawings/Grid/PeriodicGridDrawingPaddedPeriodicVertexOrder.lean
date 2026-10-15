/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Periodic.PeriodicHeightVertexOrder
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingPaddedVertexClearance

/-! # Padded crossing heights stay on the same side of every lifted vertex -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement

theorem paddedPeriodicColumnHeight_below_lifted_vertex {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (compatible : drawing.IsCompatible graph) (degree : graph.DegreeAtMost 4)
    {line : Int} {height : ℚ}
    (member : rationalResidue drawing.gridSize height ∈ verticalCrossingHeights graph drawing (line % (drawing.gridSize : Int)))
    {position : Cell} (positionMember : position ∈ drawing.vertexPositions) (cell : Cell)
    (sameX : (Cell.add position (drawing.periodTranslation cell)).1 = line)
    (below : height < ((Cell.add position (drawing.periodTranslation cell)).2 : ℚ)) :
    paddedPeriodicColumnHeight graph drawing line height <
      (paddedRefinementFactor drawing.gridSize : Int)*(Cell.add position (drawing.periodTranslation cell)).2 := by
  have inside := compatible.2.2.2.2.1 position positionMember
  have lineMod : line % (drawing.gridSize : Int) = position.1 := by
    rw [← sameX]
    simp only [Cell.add,periodTranslation,Cell.scale,Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt inside.1.le inside.2.1
  have factorPositive : (0 : Int) < paddedRefinementFactor drawing.gridSize := by exact_mod_cast paddedRefinementFactor_positive drawing.gridSize
  have finiteBounds := paddedCrossingHeight_in_cell compatible degree member
  have nonnegative : (0 : Int) ≤ crossingBound drawing.gridSize := by positivity
  have bounds : 0 < paddedCrossingHeight graph drawing (line % (drawing.gridSize : Int)) (rationalResidue drawing.gridSize height) ∧
      paddedCrossingHeight graph drawing (line % (drawing.gridSize : Int)) (rationalResidue drawing.gridSize height) <
        (paddedRefinementFactor drawing.gridSize : Int)*drawing.gridSize := by
    simpa only [paddedGridSize,Nat.cast_mul] using And.intro
      (by omega : 0 < paddedCrossingHeight graph drawing (line % (drawing.gridSize : Int)) (rationalResidue drawing.gridSize height))
      (by omega : paddedCrossingHeight graph drawing (line % (drawing.gridSize : Int)) (rationalResidue drawing.gridSize height) < paddedGridSize drawing.gridSize)
  have ordered := periodicRedistributedHeight_below_vertex (vertexRow := cell.2) factorPositive
    ⟨inside.2.2.1,inside.2.2.2⟩ (paddedCrossingHeight graph drawing (line % (drawing.gridSize : Int))) height bounds
    (fun residueBelow => by
      have gap := paddedCrossingHeight_below_vertex compatible degree member positionMember lineMod.symm residueBelow
      omega)
    (by simpa [Cell.add,periodTranslation,Cell.scale] using below)
  simpa only [paddedPeriodicColumnHeight,paddedGridSize,Nat.cast_mul,Cell.add,periodTranslation,Cell.scale] using ordered

theorem paddedPeriodicColumnHeight_above_lifted_vertex {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (compatible : drawing.IsCompatible graph) (degree : graph.DegreeAtMost 4)
    {line : Int} {height : ℚ}
    (member : rationalResidue drawing.gridSize height ∈ verticalCrossingHeights graph drawing (line % (drawing.gridSize : Int)))
    {position : Cell} (positionMember : position ∈ drawing.vertexPositions) (cell : Cell)
    (sameX : (Cell.add position (drawing.periodTranslation cell)).1 = line)
    (above : ((Cell.add position (drawing.periodTranslation cell)).2 : ℚ) ≤ height) :
    (paddedRefinementFactor drawing.gridSize : Int)*(Cell.add position (drawing.periodTranslation cell)).2 <
      paddedPeriodicColumnHeight graph drawing line height := by
  have inside := compatible.2.2.2.2.1 position positionMember
  have lineMod : line % (drawing.gridSize : Int) = position.1 := by
    rw [← sameX]
    simp only [Cell.add,periodTranslation,Cell.scale,Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt inside.1.le inside.2.1
  have factorPositive : (0 : Int) < paddedRefinementFactor drawing.gridSize := by exact_mod_cast paddedRefinementFactor_positive drawing.gridSize
  have finiteBounds := paddedCrossingHeight_in_cell compatible degree member
  have nonnegative : (0 : Int) ≤ crossingBound drawing.gridSize := by positivity
  have bounds : 0 < paddedCrossingHeight graph drawing (line % (drawing.gridSize : Int)) (rationalResidue drawing.gridSize height) ∧
      paddedCrossingHeight graph drawing (line % (drawing.gridSize : Int)) (rationalResidue drawing.gridSize height) <
        (paddedRefinementFactor drawing.gridSize : Int)*drawing.gridSize := by
    simpa only [paddedGridSize,Nat.cast_mul] using And.intro
      (by omega : 0 < paddedCrossingHeight graph drawing (line % (drawing.gridSize : Int)) (rationalResidue drawing.gridSize height))
      (by omega : paddedCrossingHeight graph drawing (line % (drawing.gridSize : Int)) (rationalResidue drawing.gridSize height) < paddedGridSize drawing.gridSize)
  have ordered := periodicRedistributedHeight_above_vertex (vertexRow := cell.2) factorPositive
    ⟨inside.2.2.1,inside.2.2.2⟩ (paddedCrossingHeight graph drawing (line % (drawing.gridSize : Int))) height bounds
    (fun residueAbove => by
      have gap := paddedCrossingHeight_above_vertex compatible degree member positionMember lineMod.symm residueAbove
      omega)
    (by simpa [Cell.add,periodTranslation,Cell.scale] using above)
  simpa only [paddedPeriodicColumnHeight,paddedGridSize,Nat.cast_mul,Cell.add,periodTranslation,Cell.scale] using ordered

end LeanTrominoes.PeriodicGridDrawing
