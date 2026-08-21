/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeCNF

/-! # Width-three conversion is only an injective literal lift -/

namespace LeanTrominoes
namespace PeriodicThreeCNF

/-- Pointwise literal lifting of one already-short clause. -/
def liftClause {Variable : Type*} (clause : PeriodicClause Variable) :
    PeriodicClause (ThreeCNFVariable Variable) :=
  clause.map liftLiteral

/-- Pointwise literal lifting of an already-width-three formula. -/
def liftFormula {Variable : Type*} (source : PeriodicCNF Variable) :
    PeriodicCNF (ThreeCNFVariable Variable) where
  clauses := source.clauses.map liftClause

/-- No auxiliary clause or variable is introduced for a clause of length at
most three. -/
theorem clauseClauses_eq_singleton_liftClause_of_le_three
    {Variable : Type*} (clause : PeriodicClause Variable)
    (width : clause.length ≤ 3) :
    clauseClauses clause = [liftClause clause] := by
  rcases clause with _ | ⟨first, rest⟩
  · rfl
  · cases rest with
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

/-- On a width-three source, `formula` preserves the complete clause and
literal order and merely injects every atom into `Sum.inl`. -/
theorem formula_eq_liftFormula_of_widthAtMostThree
    {Variable : Type*} (source : PeriodicCNF Variable)
    (width : source.WidthAtMost 3) :
    formula source = liftFormula source := by
  rcases source with ⟨clauses⟩
  unfold formula liftFormula
  congr 1
  induction clauses with
  | nil => rfl
  | cons clause clauses induction =>
      have clauseWidth : clause.length ≤ 3 :=
        width clause (by simp)
      have tailWidth : (PeriodicCNF.mk clauses).WidthAtMost 3 := by
        intro member membership
        exact width member (by simp [membership])
      rw [List.flatMap_cons,
        clauseClauses_eq_singleton_liftClause_of_le_three
          clause clauseWidth,
        induction tailWidth]
      rfl

end PeriodicThreeCNF
end LeanTrominoes
