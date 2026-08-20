/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFClauseProfileOccurrenceSplitSemantics
import LeanTrominoes.PeriodicThreeCNFExactSize

/-! # Clause profiles are preserved by vacuous width-three conversion -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace ClauseProfileThreeCNF

open ClauseProfileOccurrenceSplit

@[simp] theorem literalProfiles_liftLiteral
    {Variable : Type} (literal : PeriodicLiteral Variable) :
    literalProfiles (Variable := ThreeCNFVariable Variable)
        [PeriodicThreeCNF.liftLiteral literal] =
      literalProfiles [literal] := by
  simp [literalProfiles, PeriodicThreeCNF.liftLiteral]

theorem clauseClauses_literalProfiles_of_le_three
    {Variable : Type} (clause : PeriodicClause Variable)
    (width : clause.length ≤ 3) :
    (PeriodicThreeCNF.clauseClauses clause).map literalProfiles =
      [literalProfiles clause] := by
  rcases clause with _ | ⟨first, rest⟩
  · rfl
  · cases rest with
    | nil =>
        simp [PeriodicThreeCNF.clauseClauses, literalProfiles,
          PeriodicThreeCNF.liftLiteral]
    | cons second rest =>
        cases rest with
        | nil =>
            simp [PeriodicThreeCNF.clauseClauses, literalProfiles,
              PeriodicThreeCNF.liftLiteral]
        | cons third rest =>
            cases rest with
            | nil =>
                simp [PeriodicThreeCNF.clauseClauses, literalProfiles,
                  PeriodicThreeCNF.liftLiteral]
            | cons fourth rest =>
                simp only [List.length_cons] at width
                omega

/-- On an already width-three formula, the standard 3CNF conversion keeps
the exact polarity-and-slice profile of every clause in order. -/
theorem formula_literalProfiles_of_widthAtMostThree
    {Variable : Type} (source : PeriodicCNF Variable)
    (width : source.WidthAtMost 3) :
    (PeriodicThreeCNF.formula source).clauses.map literalProfiles =
      source.clauses.map literalProfiles := by
  rcases source with ⟨clauses⟩
  induction clauses with
  | nil => rfl
  | cons clause clauses induction =>
      have clauseWidth : clause.length ≤ 3 := width clause (by simp)
      have tailWidth : (PeriodicCNF.mk clauses).WidthAtMost 3 := by
        intro member membership
        exact width member (by simp [membership])
      unfold PeriodicThreeCNF.formula
      simp only [List.flatMap_cons, List.map_append, List.map_cons]
      have tail := induction tailWidth
      unfold PeriodicThreeCNF.formula at tail
      rw [clauseClauses_literalProfiles_of_le_three clause clauseWidth,
        tail]
      rfl

end ClauseProfileThreeCNF
end PeriodicCNF
end LeanTrominoes
