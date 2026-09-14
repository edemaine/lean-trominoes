/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionOrientationInterface
import LeanTrominoes.CompletionISquareCompiler

/-! # Compiling finite periodic orientation drawings into I-tromino prefills -/

noncomputable section
namespace LeanTrominoes.CompletionPattern.IBricks
open Gadget Gadget.PeriodicOrthogonalDrawing LBricks

set_option maxHeartbeats 2000000

def drawingDomain (drawing : PeriodicOrthogonalDrawing) : PeriodicPattern :=
  ⟨64 * (drawing.horizontalPeriodPred + 1) - 1,64 * (drawing.verticalPeriodPred + 1) - 1,[]⟩

@[simp] theorem drawingDomain_width (d : PeriodicOrthogonalDrawing) :
    (drawingDomain d).width = 64 * (d.horizontalPeriodPred + 1) := by
  dsimp [drawingDomain,PeriodicPattern.width]
  omega

@[simp] theorem drawingDomain_height (d : PeriodicOrthogonalDrawing) :
    (drawingDomain d).height = 64 * (d.verticalPeriodPred + 1) := by
  dsimp [drawingDomain,PeriodicPattern.height]
  omega

theorem getAt_repeat (d : PeriodicOrthogonalDrawing) (c : Cell) (i j : Int) :
    d.getAt (c.1 + i * (d.horizontalPeriodPred + 1),c.2 + j * (d.verticalPeriodPred + 1)) = d.getAt c := by
  unfold getAt positionAt residue
  simp [Int.add_emod]

theorem macro_palette_periodic (d : PeriodicOrthogonalDrawing) (c : Cell) (i j : Int) :
    Circuit.macroPalette (drawingKinds d) ((drawingDomain d).repeatSite c i j) =
      Circuit.macroPalette (drawingKinds d) c := by
  have index : Circuit.macroIndex ((drawingDomain d).repeatSite c i j) =
      ((Circuit.macroIndex c).1 + i * (d.horizontalPeriodPred + 1),
        (Circuit.macroIndex c).2 + j * (d.verticalPeriodPred + 1)) := by
    apply Prod.ext <;> simp only [Circuit.macroIndex,PeriodicPattern.repeatSite,drawingDomain_width,drawingDomain_height,Int.natCast_mul,Int.natCast_add,Nat.cast_ofNat,Nat.cast_one]
    · rw [show i * (64 * ((d.horizontalPeriodPred : Int) + 1)) = (i * (d.horizontalPeriodPred + 1)) * 64 by ring,Int.add_mul_ediv_right _ _ (by decide)]
    · rw [show j * (64 * ((d.verticalPeriodPred : Int) + 1)) = (j * (d.verticalPeriodPred + 1)) * 64 by ring,Int.add_mul_ediv_right _ _ (by decide)]
  have localEq : Circuit.macroLocal ((drawingDomain d).repeatSite c i j) = Circuit.macroLocal c := by
    apply Prod.ext <;> simp only [Circuit.macroLocal,PeriodicPattern.repeatSite,drawingDomain_width,drawingDomain_height,Int.natCast_mul,Int.natCast_add,Nat.cast_ofNat,Nat.cast_one]
    · rw [show i * (64 * ((d.horizontalPeriodPred : Int) + 1)) = (i * (d.horizontalPeriodPred + 1)) * 64 by ring]
      simp [Int.add_emod]
    · rw [show j * (64 * ((d.verticalPeriodPred : Int) + 1)) = (j * (d.verticalPeriodPred + 1)) * 64 by ring]
      simp [Int.add_emod]
  unfold Circuit.macroPalette
  rw [index,localEq]
  unfold drawingKinds
  rw [getAt_repeat]

def compileDrawing (drawing : PeriodicOrthogonalDrawing) : PeriodicTrominoPrefill :=
  (drawingDomain drawing).compileSquare (Circuit.macroPalette (drawingKinds drawing))

theorem squareHolds_iff_lSquareHolds (palette : Cell → Fin 24) :
    SquareHolds palette ↔ LBricks.SquareHolds palette := Iff.rfl

/-- Exact finite reduction; completing tilings need not be periodic. -/
theorem compileDrawing_correct (drawing : PeriodicOrthogonalDrawing) (wf : drawing.IsWellFormed) :
    PeriodicTrominoPrefill.planeProblem .I (compileDrawing drawing) ↔ drawing.HasOrientation := by
  rw [compileDrawing,PeriodicPattern.compileSquare_correct _ _ (macro_palette_periodic drawing)]
  rw [squareHolds_iff_lSquareHolds,← Circuit.macro_reduction_correct,← drawing_source_correct drawing wf]

end LeanTrominoes.CompletionPattern.IBricks
