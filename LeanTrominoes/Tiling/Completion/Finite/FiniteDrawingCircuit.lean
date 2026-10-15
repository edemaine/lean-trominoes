/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Completion.Finite.FiniteCircuitRectangle
import LeanTrominoes.Tiling.Completion.CompletionOrientationInterface
import LeanTrominoes.Tiling.Tromino.Finite.FiniteGadgetSubstitution

/-! # Finite orientation drawings as finite-support circuit sources -/
noncomputable section
namespace LeanTrominoes.CompletionPattern.LBricks
open Gadget Gadget.PeriodicOrthogonalDrawing Circuit

/-- All cells outside the one finite drawing rectangle are blank. -/
def finiteDrawingKinds (drawing : PeriodicOrthogonalDrawing) : Cell → CircuitKind :=
  cutDomain (rectangleInside drawing.horizontalPeriod drawing.verticalPeriod) (drawingKinds drawing)

theorem drawingKinds_wrapRectangle (drawing : PeriodicOrthogonalDrawing) (location : Cell) :
    drawingKinds drawing (wrapRectangle drawing.horizontalPeriod drawing.verticalPeriod location)=
      drawingKinds drawing location := by
  unfold drawingKinds getAt
  congr 2
  apply Prod.ext <;> apply Fin.ext <;>
    simp [positionAt,residue,wrapRectangle,horizontalPeriod,verticalPeriod,Int.emod_emod]

theorem drawingKinds_blank_last (drawing : PeriodicOrthogonalDrawing)
    (boundary : drawing.BlankBoundary) (location : Cell)
    (edge : location.1%(drawing.horizontalPeriod:Int)=(drawing.horizontalPeriod:Int)-1 ∨
      location.2%(drawing.verticalPeriod:Int)=(drawing.verticalPeriod:Int)-1) :
    drawingKinds drawing location=.blank := by
  have last : (drawing.positionAt location).1.val+1=drawing.horizontalPeriod ∨
      (drawing.positionAt location).2.val+1=drawing.verticalPeriod := by
    rcases edge with horizontal|vertical
    · left
      have val := residue_val_int location.1 drawing.horizontalPeriodPred
      change ((drawing.positionAt location).1.val:Int)=_ at val
      change _=(drawing.horizontalPeriod:Int)-1 at horizontal
      change ((drawing.positionAt location).1.val:Int)=location.1%(drawing.horizontalPeriod:Int) at val
      omega
    · right
      have val := residue_val_int location.2 drawing.verticalPeriodPred
      change ((drawing.positionAt location).2.val:Int)=_ at val
      change _=(drawing.verticalPeriod:Int)-1 at vertical
      change ((drawing.positionAt location).2.val:Int)=location.2%(drawing.verticalPeriod:Int) at val
      omega
  simp only [drawingKinds,getAt,boundary _ last,kindOf]

/-- Cutting a blank-bordered drawing preserves all orientation constraints. -/
theorem finiteDrawingKinds_correct (drawing : PeriodicOrthogonalDrawing)
    (wellFormed : drawing.IsWellFormed) (boundary : drawing.BlankBoundary) :
    drawing.HasOrientation ↔ SourceHolds (finiteDrawingKinds drawing) := by
  rw [drawing_source_correct drawing wellFormed]
  exact (source_rectangle_iff drawing.horizontalPeriod drawing.verticalPeriod
    (by dsimp [horizontalPeriod]; omega) (by dsimp [verticalPeriod]; omega)
    (drawingKinds drawing) (drawingKinds_wrapRectangle drawing)
    (drawingKinds_blank_last drawing boundary)).symm
end LeanTrominoes.CompletionPattern.LBricks
