/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Tromino.Finite.FiniteProgramCompletionCompiler

/-! # NP-completeness of finite-preplacement tromino plane completion -/
namespace LeanTrominoes.Tromino.FiniteCoordinateColumns
open Complexity FiniteProgramCompletion

/-- Finite preplacements of either single tromino are NP-hard to complete. -/
theorem completion_npHard (t : Tromino) :
    NPHard (completionEncoding t)
      (fun prefill => t.Completable Set.univ ((completionFootprints t prefill).toFinset : Set (Finset Cell))) := by
  intro Source sourceEncoding language inNP
  obtain ⟨verifier⟩ := inNP
  let source := FiniteNPProgramSource.source verifier
  let zero := FiniteNPProgramSource.formula_zero verifier
  exact PolyTimeManyOneReducible.of_computableInPolyTime (prefill source zero t)
    ⟨prefillComputableInPolyTime source zero t⟩ (correct source zero t)

/-- Theorem 5.12: completion is NP-complete when the encoding charges for the
polynomial bounding box, for both I- and L-trominoes. -/
theorem completion_npComplete (t : Tromino) :
    NPComplete (completionEncoding t)
      (fun prefill => t.Completable Set.univ ((completionFootprints t prefill).toFinset : Set (Finset Cell))) :=
  ⟨completion_inNP t,completion_npHard t⟩
end LeanTrominoes.Tromino.FiniteCoordinateColumns
