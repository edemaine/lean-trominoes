/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreeToThreeDMOccurrences

/-!
# Degree-three variables come from the source

Both exact-one transformations introduce fresh clause-local variables, but
each such auxiliary occurs at most twice.  Consequently, any output variable
that reaches the third occurrence slot is an embedded source variable.  This
is the structural fact needed to transport source-variable fan order through
the two transformations.
-/

namespace LeanTrominoes

/-- Counts computed by two equality-correct Boolean equality procedures
coincide.  This bridges the decidable-equality instance used by occurrence
filtering with the componentwise `BEq` instance on a sum type. -/
private theorem count_eq_of_beq_iff_eq {α : Type*}
    (first second : BEq α)
    (firstLawful : ∀ a b : α,
      @BEq.beq α first a b = true ↔ a = b)
    (secondLawful : ∀ a b : α,
      @BEq.beq α second a b = true ↔ a = b)
    (value : α) (values : List α) :
    @List.count α first value values =
      @List.count α second value values := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.count_cons]
      have beqEq :
          @BEq.beq α first head value =
            @BEq.beq α second head value := by
        apply Bool.eq_iff_iff.mpr
        exact (firstLawful head value).trans
          (secondLawful head value).symm
      rw [beqEq, induction]

namespace PeriodicOneInThree

/-- A variable of the Figure 7 exact-one formula that reaches the third
occurrence slot is an embedded source variable, not a fresh auxiliary. -/
theorem exists_original_of_occurrenceAt_third
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (output : OneInThreeVariable Variable)
    (tagged :
      PeriodicOneInThreeToThreeDM.TaggedOccurrence
        (OneInThreeVariable Variable))
    (lookup :
      PeriodicOneInThreeToThreeDM.occurrenceAt
          (formula source) output .third = some tagged) :
    ∃ atom, output = Sum.inl atom := by
  cases output with
  | inl atom =>
      exact ⟨atom, rfl⟩
  | inr auxiliary =>
      rcases auxiliary with
        ⟨⟨clauseIndex, sourceClause⟩, kind⟩
      have threeLe :=
        PeriodicOneInThreeToThreeDM.three_le_variableOccurrences_count_of_occurrenceAt_third
          (formula source)
          (Sum.inr ((clauseIndex, sourceClause), kind)) tagged lookup
      have countEq :
          @List.count (OneInThreeVariable Variable)
              instBEqOfDecidableEq
              (Sum.inr ((clauseIndex, sourceClause), kind))
              (PeriodicCNF.variableOccurrences (formula source)) =
            @List.count (OneInThreeVariable Variable)
              Sum.instBEq
              (Sum.inr ((clauseIndex, sourceClause), kind))
              (PeriodicCNF.variableOccurrences (formula source)) := by
        apply count_eq_of_beq_iff_eq
        · intro a b
          exact
            @beq_iff_eq _ instBEqOfDecidableEq inferInstance a b
        · intro a b
          exact @beq_iff_eq _ Sum.instBEq inferInstance a b
      rw [countEq] at threeLe
      have twoLe :=
        formula_variableOccurrences_count_auxiliary_le_two
          source clauseIndex sourceClause kind
      omega

end PeriodicOneInThree

namespace PeriodicOneInThreeNoUnits

/-- A variable of the unit-free exact-one formula that reaches the third
occurrence slot is an embedded source variable, not a fresh auxiliary. -/
theorem exists_original_of_occurrenceAt_third
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (output : OneInThreeNoUnitVariable Variable)
    (tagged :
      PeriodicOneInThreeToThreeDM.TaggedOccurrence
        (OneInThreeNoUnitVariable Variable))
    (lookup :
      PeriodicOneInThreeToThreeDM.occurrenceAt
          (formula source) output .third = some tagged) :
    ∃ atom, output = Sum.inl atom := by
  cases output with
  | inl atom =>
      exact ⟨atom, rfl⟩
  | inr auxiliary =>
      rcases auxiliary with
        ⟨⟨clauseIndex, sourceClause⟩, kind⟩
      have threeLe :=
        PeriodicOneInThreeToThreeDM.three_le_variableOccurrences_count_of_occurrenceAt_third
          (formula source)
          (Sum.inr ((clauseIndex, sourceClause), kind)) tagged lookup
      have countEq :
          @List.count (OneInThreeNoUnitVariable Variable)
              instBEqOfDecidableEq
              (Sum.inr ((clauseIndex, sourceClause), kind))
              (PeriodicCNF.variableOccurrences (formula source)) =
            @List.count (OneInThreeNoUnitVariable Variable)
              Sum.instBEq
              (Sum.inr ((clauseIndex, sourceClause), kind))
              (PeriodicCNF.variableOccurrences (formula source)) := by
        apply count_eq_of_beq_iff_eq
        · intro a b
          exact
            @beq_iff_eq _ instBEqOfDecidableEq inferInstance a b
        · intro a b
          exact @beq_iff_eq _ Sum.instBEq inferInstance a b
      rw [countEq] at threeLe
      have twoLe :=
        formula_variableOccurrences_count_auxiliary_le_two
          source clauseIndex sourceClause kind
      omega

end PeriodicOneInThreeNoUnits

end LeanTrominoes
