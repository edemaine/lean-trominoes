/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFOneDimensional
import LeanTrominoes.PeriodicOneInThreeNoUnits

/-!
# One-dimensional exact-one unit elimination

The unit-elimination auxiliaries use their source clause's first-literal
anchor.  Nonunit clauses are embedded with unchanged offsets, so eliminating
exact-one unit clauses preserves the one-dimensional fragment.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreeNoUnits

/-- Every clause generated from one horizontally supported exact-one clause
has only zero vertical offsets. -/
theorem clauseClauses_areOneDimensional
    {Variable : Type*}
    (clauseIndex : Nat)
    (source : PeriodicClause Variable)
    (horizontal : ∀ literal ∈ source, literal.offset.2 = 0) :
    ∀ generated ∈ clauseClauses clauseIndex source,
      ∀ literal ∈ generated, literal.offset.2 = 0 := by
  cases source with
  | nil =>
      intro generated generatedMember literal literalMember
      simp only [clauseClauses, List.mem_cons, List.not_mem_nil, or_false]
        at generatedMember
      rcases generatedMember with rfl | rfl | rfl <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false]
          at literalMember <;>
        rcases literalMember with rfl | rfl <;> rfl
  | cons first rest =>
      cases rest with
      | nil =>
          have firstVertical := horizontal first (by simp)
          intro generated generatedMember literal literalMember
          simp only [clauseClauses, List.mem_cons, List.not_mem_nil, or_false]
            at generatedMember
          rcases generatedMember with rfl | rfl
          · simp only [List.mem_cons, List.not_mem_nil, or_false]
              at literalMember
            rcases literalMember with rfl | rfl | rfl <;>
              simpa [PeriodicOneInThree.negate, liftLiteral, auxiliary,
                PeriodicOneInThree.anchor] using firstVertical
          · simp only [List.mem_cons, List.not_mem_nil, or_false]
              at literalMember
            rcases literalMember with rfl | rfl <;>
              simpa [auxiliary, PeriodicOneInThree.anchor] using firstVertical
      | cons second rest =>
          intro generated generatedMember literal literalMember
          simp only [clauseClauses, List.mem_singleton] at generatedMember
          subst generated
          simp only [List.mem_map] at literalMember
          obtain ⟨sourceLiteral, sourceLiteralMember, rfl⟩ := literalMember
          simpa [liftLiteral] using
            horizontal sourceLiteral sourceLiteralMember

/-- Exact-one unit elimination preserves one-dimensionality. -/
theorem formula_isOneDimensional
    {Variable : Type*}
    {source : PeriodicCNF Variable}
    (horizontal : source.IsOneDimensional) :
    (formula source).IsOneDimensional := by
  intro clause clauseMember literal literalMember
  simp only [formula, List.mem_flatMap] at clauseMember
  obtain ⟨taggedClause, taggedClauseMember, clauseMember⟩ := clauseMember
  exact clauseClauses_areOneDimensional taggedClause.2 taggedClause.1
    (horizontal taggedClause.1
      (List.fst_mem_of_mem_zipIdx taggedClauseMember))
    clause clauseMember literal literalMember

end PeriodicOneInThreeNoUnits
end LeanTrominoes
