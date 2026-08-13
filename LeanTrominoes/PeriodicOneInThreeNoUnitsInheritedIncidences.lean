/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreeNoUnits

/-!
# Source incidences inherited by unit elimination

Every `.inl` literal in a generated unit-elimination clause comes from one
precise source literal occurrence.  Its atom and periodic offset are
unchanged; a unit source literal has only its polarity negated.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreeNoUnits

/-- Classify an inherited unit-elimination literal by its source literal and
source presentation index. -/
theorem inherited_of_mem_clauseClauses
    {Variable : Type*}
    (clauseIndex : Nat)
    (source : PeriodicClause Variable)
    {clause :
      PeriodicClause (OneInThreeNoUnitVariable Variable)}
    (clauseMember : clause ∈ clauseClauses clauseIndex source)
    {literal :
      PeriodicLiteral (OneInThreeNoUnitVariable Variable)}
    (literalMember : literal ∈ clause)
    (sourceAtom : Variable)
    (literalSource : literal.atom = .inl sourceAtom) :
    ∃ sourceLiteral sourceLiteralIndex,
      (sourceLiteral, sourceLiteralIndex) ∈ source.zipIdx ∧
        sourceLiteral.atom = sourceAtom ∧
        literal.offset = sourceLiteral.offset := by
  rcases source with _ | ⟨first, rest⟩
  · simp only [clauseClauses, List.mem_cons,
      List.not_mem_nil, or_false] at clauseMember
    rcases clauseMember with rfl | rfl | rfl <;>
      simp only [List.mem_cons, List.not_mem_nil,
        or_false] at literalMember <;>
      rcases literalMember with rfl | rfl <;>
      simp [auxiliary] at literalSource
  · rcases rest with _ | ⟨second, tail⟩
    · simp only [clauseClauses, List.mem_cons,
        List.not_mem_nil, or_false] at clauseMember
      rcases clauseMember with rfl | rfl <;>
        simp_all [auxiliary, liftLiteral,
          PeriodicOneInThree.negate] <;>
        aesop
    · simp only [clauseClauses, List.mem_singleton]
        at clauseMember
      subst clause
      simp only [List.mem_map] at literalMember
      rcases literalMember with
        ⟨sourceLiteral, sourceLiteralMember, rfl⟩
      rcases List.mem_iff_getElem.mp sourceLiteralMember with
        ⟨sourceLiteralIndex, sourceLiteralIndexLt,
          sourceLiteralAt⟩
      refine
        ⟨sourceLiteral, sourceLiteralIndex, ?_, ?_, rfl⟩
      · rw [List.mem_zipIdx_iff_getElem?,
          List.getElem?_eq_some_iff]
        exact ⟨sourceLiteralIndexLt, sourceLiteralAt⟩
      · simpa [liftLiteral] using literalSource

end PeriodicOneInThreeNoUnits
end LeanTrominoes
