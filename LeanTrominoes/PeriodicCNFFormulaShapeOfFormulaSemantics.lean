/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeOfFormulaData

/-! # Exact semantics of canonical concrete formula shapes -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeOfFormula

open ClauseProfileOccurrenceSplit
open UnaryProgramClauseProfile

theorem clauseProfile_literals
    (literals : List LiteralProfile)
    (nonempty : literals ≠ []) (width : literals.length ≤ 3) :
    (clauseProfile literals).literals = literals := by
  cases literals with
  | nil => exact (nonempty rfl).elim
  | cons first rest =>
      cases rest with
      | nil => rfl
      | cons second rest =>
          cases rest with
          | nil => rfl
          | cons third rest =>
              cases rest with
              | nil => rfl
              | cons fourth rest =>
                  simp only [List.length_cons] at width
                  omega

/-- For a nonempty width-three presentation, the canonical shape records the
exact polarity/current-next profile of every clause and the exact number of
distinct variables. -/
theorem shape_correct
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (width : formula.WidthAtMost 3)
    (nonempty : ∀ clause ∈ formula.clauses, clause ≠ []) :
    CorrectFor (shape formula) formula := by
  unfold CorrectFor
  constructor
  · rw [clauseProfiles_shape]
    unfold profiles
    rw [List.map_map]
    apply List.map_congr_left
    intro clause clauseMem
    exact clauseProfile_literals (literalProfiles clause)
      (by
        intro profilesEmpty
        have clauseEmpty : clause = [] := by
          simpa [literalProfiles] using profilesEmpty
        exact nonempty clause clauseMem clauseEmpty)
      (by
        rw [show (literalProfiles clause).length = clause.length by
          simp [literalProfiles]]
        exact width clause clauseMem)
  · exact variableCount_shape formula

end FormulaShapeOfFormula
end PeriodicCNF
end LeanTrominoes
