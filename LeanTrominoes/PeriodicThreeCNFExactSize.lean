/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeCNFSize

/-! # Exact size preservation on formulas already of width three -/

namespace LeanTrominoes
namespace PeriodicThreeCNF

@[simp] theorem clauseClauses_length_of_le_three {Variable : Type*}
    (clause : PeriodicClause Variable) (width : clause.length ≤ 3) :
    (clauseClauses clause).length = 1 := by
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
            | cons fourth rest => simp at width

@[simp] theorem clauseClauses_flatten_length_of_le_three
    {Variable : Type*} (clause : PeriodicClause Variable)
    (width : clause.length ≤ 3) :
    (clauseClauses clause).flatten.length = clause.length := by
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
            | cons fourth rest => simp at width

/-- Width-three conversion preserves the number of clauses when no clause
actually exceeds width three. -/
@[simp] theorem formula_clauses_length_of_widthAtMostThree
    {Variable : Type*} (source : PeriodicCNF Variable)
    (width : source.WidthAtMost 3) :
    (formula source).clauses.length = source.clauses.length := by
  rcases source with ⟨clauses⟩
  induction clauses with
  | nil => rfl
  | cons clause clauses induction =>
      have headWidth : clause.length ≤ 3 := width clause (by simp)
      have tailWidth : (PeriodicCNF.mk clauses).WidthAtMost 3 := by
        intro member membership
        exact width member (by simp [membership])
      simp only [formula, List.flatMap_cons, List.length_append,
        List.length_cons]
      rw [clauseClauses_length_of_le_three clause headWidth]
      have tailLength := induction tailWidth
      change (clauses.flatMap clauseClauses).length =
        clauses.length at tailLength
      rw [tailLength]
      omega

/-- Width-three conversion also preserves the exact literal-occurrence
count on an already width-three presentation. -/
@[simp] theorem formula_presentationLiteralCount_of_widthAtMostThree
    {Variable : Type*} (source : PeriodicCNF Variable)
    (width : source.WidthAtMost 3) :
    PeriodicCNF.presentationLiteralCount (formula source) =
      PeriodicCNF.presentationLiteralCount source := by
  rcases source with ⟨clauses⟩
  induction clauses with
  | nil => rfl
  | cons clause clauses induction =>
      have headWidth : clause.length ≤ 3 := width clause (by simp)
      have tailWidth : (PeriodicCNF.mk clauses).WidthAtMost 3 := by
        intro member membership
        exact width member (by simp [membership])
      unfold formula PeriodicCNF.presentationLiteralCount
      simp only [List.flatMap_cons, List.flatten_append,
        List.length_append, List.flatten_cons]
      rw [clauseClauses_flatten_length_of_le_three clause headWidth]
      rw [show (List.flatten (clauses.flatMap clauseClauses)).length =
          (List.flatten clauses).length by
        exact induction tailWidth]

end PeriodicThreeCNF
end LeanTrominoes
