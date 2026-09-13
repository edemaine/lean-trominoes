/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TallSlabVoxelCompiler

/-! # Every source presentation compiles correctly for every fixed taller slab -/

namespace LeanTrominoes.TwoConnectedPolycubes.TallSlabCompiler

open KeyedPeriodicComplement

theorem compile_source_correct {height : Nat} (hh : 3 ≤ height)
    {problem : PeriodicThreeDM} (presentation : problem.PlanarPresentation) :
    slabProblem height (compile height (Theorem55Compiler.sourceInput presentation)) ↔
      Tromino.I.Tileable (presentation.normalizedOrthogonalDrawing.periodicRegion .I).carrier := by
  let n := 3*Theorem55Source.period presentation
  have large := Theorem55Source.period_large presentation
  have hn : 96 ≤ n := by dsimp [n]; omega
  have positive : 0 < n := by omega
  have multiple : (n : Int) % 3 = 0 := by simp [n,Int.mul_emod]
  have wide : height < (height+1)*n := by
    have := Nat.le_mul_of_pos_right (height+1) positive
    omega
  have largePeriod : 96 ≤ (height+1)*n := hn.trans (Nat.le_mul_of_pos_left n (by omega))
  have newMultiple : (((height+1)*n : Nat) : Int) % 3 = 0 := by
    simp [Nat.cast_mul,Int.mul_emod,multiple]
  have carrier : holesRegion ((height+1)*n)
      (repeatMask (height+1) n (Theorem55Source.holes presentation)) =
      PlusRefinement.region (Theorem55Source.region presentation) :=
    (repeatMask_carrier (by omega) positive _).trans (Theorem55Source.holes_carrier presentation)
  exact (slabProblem_iff_of_mask hh wide largePeriod newMultiple
    (repeatMask (height+1) n (Theorem55Source.holes presentation))
    (repeatMask_admissible hn multiple _ (Theorem55Source.holes_admissible presentation))
    (Theorem55Source.region presentation) carrier _ (compile_source height presentation)).trans
      (Theorem55Source.tileable_iff presentation)

end LeanTrominoes.TwoConnectedPolycubes.TallSlabCompiler
