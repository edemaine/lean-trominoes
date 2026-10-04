/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteDrawingCircuit
import LeanTrominoes.FiniteLSquarePrefill
import LeanTrominoes.FiniteISquarePrefill
import LeanTrominoes.CompletionIOrientationCompiler

/-! # Finite preplacements for finite blank-bordered orientation drawings -/
noncomputable section
namespace LeanTrominoes.CompletionPattern
open Gadget Gadget.PeriodicOrthogonalDrawing LBricks LBricks.Circuit

def finiteDrawingPalette (drawing : PeriodicOrthogonalDrawing) : Cell → Fin 24 :=
  macroPalette (finiteDrawingKinds drawing)

theorem finiteDrawingPalette_blank (drawing : PeriodicOrthogonalDrawing) (c : Cell)
    (outside : ¬(0≤c.1 ∧ c.1<(64*drawing.horizontalPeriod:Int) ∧
      0≤c.2 ∧ c.2<(64*drawing.verticalPeriod:Int))) : finiteDrawingPalette drawing c=0 := by
  have notInside : ¬rectangleInside drawing.horizontalPeriod drawing.verticalPeriod (macroIndex c) := by
    dsimp [rectangleInside,macroIndex]
    omega
  simp [finiteDrawingPalette,macroPalette,finiteDrawingKinds,cutDomain,notInside,
    circuitFor,CircuitData.Blank.circuit,labelAt,lookup]

def finiteDrawingPrefill (drawing : PeriodicOrthogonalDrawing) (t : Tromino) : List (Placement Unit) :=
  match t with
  | .I => IBricks.FiniteGuards.squarePrefill (finiteDrawingPalette drawing)
      (64*drawing.horizontalPeriod) (64*drawing.verticalPeriod)
  | .L => LBricks.FiniteGuards.squarePrefill (finiteDrawingPalette drawing)
      (64*drawing.horizontalPeriod) (64*drawing.verticalPeriod)

/-- Both trominoes implement the finite orientation drawing as finitely many
preplaced tiles whose completion covers the entire plane. -/
theorem finiteDrawingPrefill_correct (drawing : PeriodicOrthogonalDrawing)
    (wellFormed : drawing.IsWellFormed) (boundary : drawing.BlankBoundary) (t : Tromino) :
    drawing.HasOrientation ↔ t.Completable Set.univ
      (((finiteDrawingPrefill drawing t).map fun p => p.cells (fun _ => t.cells)).toFinset : Set (Finset Cell)) := by
  have source := finiteDrawingKinds_correct drawing wellFormed boundary
  have macros := macro_reduction_correct (finiteDrawingKinds drawing)
  cases t
  · exact (source.trans macros).trans
      (IBricks.FiniteGuards.squarePrefill_correct (finiteDrawingPalette drawing)
        (64*drawing.horizontalPeriod) (64*drawing.verticalPeriod) (finiteDrawingPalette_blank drawing))
  · exact (source.trans macros).trans
      (LBricks.FiniteGuards.squarePrefill_correct (finiteDrawingPalette drawing)
        (64*drawing.horizontalPeriod) (64*drawing.verticalPeriod) (finiteDrawingPalette_blank drawing))
end LeanTrominoes.CompletionPattern
