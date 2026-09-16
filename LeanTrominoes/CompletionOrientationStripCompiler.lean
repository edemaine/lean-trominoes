/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionOrientationStripSource
import LeanTrominoes.CompletionDiagonalPeriod
import LeanTrominoes.CompletionLStripCompiler
import LeanTrominoes.CompletionIStripCompiler

/-! # Finite strip-completion inputs from blank-bordered orientation drawings -/
noncomputable section
namespace LeanTrominoes.CompletionPattern
open Gadget Gadget.PeriodicOrthogonalDrawing LBricks
set_option maxHeartbeats 2000000
namespace StripOrientation

def palette (d : PeriodicOrthogonalDrawing) : Cell → Fin 24 :=
  DiagonalRouting.brickPalette (Circuit.macroPalette (stripKinds d))

def period (d : PeriodicOrthogonalDrawing) : Nat := 128*d.horizontalPeriod
def count (d : PeriodicOrthogonalDrawing) : Nat := 256*(d.verticalPeriod+1)

theorem macro_support (d : PeriodicOrthogonalDrawing) (c : Cell)
    (outside : c.2 < 64 ∨ 64*(d.verticalPeriod:Int)+63 < c.2) :
    Circuit.macroPalette (stripKinds d) c = 0 := by
  have blank : stripKinds d (Circuit.macroIndex c) = .blank :=
    stripKinds_support d _ (by dsimp [Circuit.macroIndex]; omega)
  simp [Circuit.macroPalette,blank,circuitFor,CircuitData.Blank.circuit,Circuit.labelAt,Circuit.lookup]

theorem macro_periodic (d : PeriodicOrthogonalDrawing) (c : Cell) (i : Int) :
    Circuit.macroPalette (stripKinds d) (c.1+i*(64*d.horizontalPeriod),c.2) =
      Circuit.macroPalette (stripKinds d) c := by
  have index : Circuit.macroIndex (c.1+i*(64*d.horizontalPeriod),c.2) =
      ((Circuit.macroIndex c).1+i*d.horizontalPeriod,(Circuit.macroIndex c).2) := by
    apply Prod.ext
    · dsimp [Circuit.macroIndex]
      rw [show i*(64*(d.horizontalPeriod:Int)) = (i*d.horizontalPeriod)*64 by ring,
        Int.add_mul_ediv_right _ _ (by decide)]
    · rfl
  have localEq : Circuit.macroLocal (c.1+i*(64*d.horizontalPeriod),c.2) = Circuit.macroLocal c := by
    apply Prod.ext
    · dsimp [Circuit.macroLocal]
      rw [show i*(64*(d.horizontalPeriod:Int)) = (i*d.horizontalPeriod)*64 by ring]
      simp [Int.add_emod]
    · rfl
  simp only [Circuit.macroPalette,index,localEq,stripKinds_periodic]

theorem palette_periodic (d : PeriodicOrthogonalDrawing) (c : Cell) (i : Int) :
    palette d (c.1+i*period d,c.2) = palette d c := by
  have periodic := DiagonalRouting.brickPalette_period (Circuit.macroPalette (stripKinds d))
    (i*(64*d.horizontalPeriod)) (fun c => macro_periodic d c i) c
  convert periodic using 1 <;> congr 2 <;> simp [Cell.add,period] <;> ring

theorem palette_blank (d : PeriodicOrthogonalDrawing) (c : Cell)
    (outside : c.2 ≤ 0 ∨ (count d:Int) ≤ c.2) : palette d c = 0 := by
  apply DiagonalRouting.brickPalette_support _ 64 (64*d.verticalPeriod+63) (macro_support d)
  dsimp [count] at outside
  push_cast at outside
  omega

def compile (t : Tromino) (d : PeriodicOrthogonalDrawing) : PeriodicStripTrominoPrefill :=
  match t with
  | .L => LBricks.compileStrip (period d) (count d) (palette d)
  | .I => IBricks.compileStrip (period d) (count d) (palette d)

/-- Exact reduction semantics, for both trominoes and arbitrary completing tilings. -/
theorem compile_correct (t : Tromino) (d : PeriodicOrthogonalDrawing)
    (wf : d.IsWellFormed) (blank : d.HasBlankVerticalBoundary) :
    PeriodicStripTrominoPrefill.problem t (compile t d) ↔ d.HasOrientation := by
  have hp : 0 < period d := by simp [period,horizontalPeriod]
  have hn : 0 < count d := by simp [count]
  cases t
  · rw [compile,IBricks.compileStrip_correct _ _ hp hn _ (palette_periodic d) (palette_blank d),
      palette,DiagonalRouting.iCompletion_iff,← Circuit.macro_reduction_correct,stripKinds_correct d wf blank]
  · rw [compile,LBricks.compileStrip_correct _ _ hp hn _ (palette_periodic d) (palette_blank d),
      palette,DiagonalRouting.lCompletion_iff,← Circuit.macro_reduction_correct,stripKinds_correct d wf blank]
end StripOrientation
end LeanTrominoes.CompletionPattern
