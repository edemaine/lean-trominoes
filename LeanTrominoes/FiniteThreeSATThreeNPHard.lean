/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteNPThreeOccurrenceCompiler

/-! # Finite width-three occurrence-three SAT is NP-hard

The output has compact natural variable names and no empty clauses. Both
Cook–Levin compilation and occurrence splitting use actual polynomial-time
finite-alphabet machines under the native binary formula encoding.
-/
noncomputable section
namespace LeanTrominoes.FiniteCNF
open Complexity

def ThreeThreeSatisfiable (formula : Formula Nat) : Prop :=
  WidthAtMost 3 formula ∧ (periodize formula).OccurrencesAtMost 3 ∧
    (∀ clause∈formula, clause≠[]) ∧ Satisfiable formula

theorem threeThreeSatisfiable_npHard : NPHard FiniteCNFCompiler.finEncoding ThreeThreeSatisfiable := by
  intro Input encoding language member
  obtain ⟨verifier⟩ := member
  apply PolyTimeManyOneReducible.of_computableInPolyTime (FiniteNPThreeOccurrenceCompiler.formula verifier)
    ⟨FiniteNPThreeOccurrenceCompiler.computableInPolyTime verifier⟩
  intro input
  exact ⟨fun truth => ⟨FiniteNPThreeOccurrenceCompiler.width verifier input,
    FiniteNPThreeOccurrenceCompiler.occurrences verifier input,
    FiniteNPThreeOccurrenceCompiler.clauses_nonempty verifier input,
    (FiniteNPThreeOccurrenceCompiler.correct verifier input).mpr truth⟩,
    fun truth => (FiniteNPThreeOccurrenceCompiler.correct verifier input).mp truth.2.2.2⟩

end LeanTrominoes.FiniteCNF
