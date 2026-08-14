/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceGraphSize
import LeanTrominoes.PeriodicThreeCNF

/-!
# Presentation-size bounds for periodic 3CNF conversion
-/

namespace LeanTrominoes
namespace PeriodicThreeCNF

theorem continuation_length_le {Variable : Type*}
    (source remaining : PeriodicClause Variable) :
    (continuation source remaining).length ≤ remaining.length + 1 := by
  induction remaining with
  | nil => simp [continuation]
  | cons first rest induction =>
      cases rest with
      | nil => simp [continuation]
      | cons second rest =>
          cases rest with
          | nil => simp [continuation]
          | cons third rest =>
              simp only [continuation, List.length_cons]
              simp only [List.length_cons] at induction
              omega

theorem clauseClauses_length_le {Variable : Type*}
    (source : PeriodicClause Variable) :
    (clauseClauses source).length ≤ source.length + 1 := by
  rcases source with _ | ⟨first, rest⟩
  · simp [clauseClauses]
  · cases rest with
    | nil => simp [clauseClauses]
    | cons second rest =>
        cases rest with
        | nil => simp [clauseClauses]
        | cons third rest =>
            cases rest with
            | nil => simp [clauseClauses]
            | cons fourth rest =>
                simp only [clauseClauses, List.length_cons]
                have tail := continuation_length_le
                  (first :: second :: third :: fourth :: rest)
                  (third :: fourth :: rest)
                simp only [List.length_cons] at tail
                omega

theorem formula_clauses_length_le_presentationSize
    {Variable : Type*} (source : PeriodicCNF Variable) :
    (formula source).clauses.length ≤
      PeriodicCNF.presentationSize source := by
  rcases source with ⟨clauses⟩
  change (clauses.flatMap clauseClauses).length ≤
    clauses.length + clauses.flatten.length
  induction clauses with
  | nil => simp
  | cons clause clauses induction =>
      simp only [List.flatMap_cons, List.length_append,
        List.length_cons, List.flatten_cons]
      have head := clauseClauses_length_le clause
      omega

/-- Width-three conversion grows the finite presentation by at most a fixed
factor, independent of literal values and offsets. -/
theorem formula_presentationSize_le
    {Variable : Type*} (source : PeriodicCNF Variable) :
    PeriodicCNF.presentationSize (formula source) ≤
      4 * PeriodicCNF.presentationSize source := by
  have clauses := formula_clauses_length_le_presentationSize source
  have literals := PeriodicCNF.presentationLiteralCount_le_mul_of_width
    (formula source) 3 (formula_widthAtMostThree source)
  unfold PeriodicCNF.presentationSize at clauses literals ⊢
  omega

end PeriodicThreeCNF
end LeanTrominoes
