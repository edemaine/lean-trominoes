/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteProgramTrominoRegionCompiler
import LeanTrominoes.FiniteTrominoRegionInNP

/-! # NP-completeness of finite I- and L-tromino region tiling -/
namespace LeanTrominoes.Tromino.FiniteCoordinateColumns
open Complexity FiniteProgramSparseTrominoRegion

/-- Every NP verifier reduces to a finite region tileable by the selected
single tromino. No source-emitter hypothesis remains. -/
theorem region_npHard (t : Tromino) :
    NPHard regionEncoding (fun cells => t.Tileable (cells.toFinset:Set Cell)) := by
  intro Source sourceEncoding language inNP
  obtain ⟨verifier⟩ := inNP
  let source := FiniteNPProgramSource.source verifier
  let zero := FiniteNPProgramSource.formula_zero verifier
  exact PolyTimeManyOneReducible.of_computableInPolyTime (region source t)
    ⟨regionComputableInPolyTime source zero t⟩ (correct source zero t)

/-- Corollary 5.4: finite-region tiling is NP-complete for either tromino. -/
theorem region_npComplete (t : Tromino) :
    NPComplete regionEncoding (fun cells => t.Tileable (cells.toFinset:Set Cell)) :=
  ⟨region_inNP t,region_npHard t⟩
end LeanTrominoes.Tromino.FiniteCoordinateColumns
