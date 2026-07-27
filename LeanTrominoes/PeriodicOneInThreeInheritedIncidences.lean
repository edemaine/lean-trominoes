import LeanTrominoes.PeriodicOneInThree

/-!
# Source incidences inherited by Figure 9

Every `.inl` literal in a generated Figure 9 clause comes from one precise
literal occurrence of the source clause.  Its atom and periodic offset are
unchanged; only the polarity of the second and third source literals is
negated inside the gadget.
-/

namespace LeanTrominoes
namespace PeriodicOneInThree

/-- Classify an inherited Figure 9 literal by its source literal and source
presentation index. -/
theorem inherited_of_mem_clauseClauses
    {Variable : Type*}
    (clauseIndex : Nat)
    (source : PeriodicClause Variable)
    {clause : PeriodicClause (OneInThreeVariable Variable)}
    (clauseMember : clause ∈ clauseClauses clauseIndex source)
    {literal : PeriodicLiteral (OneInThreeVariable Variable)}
    (literalMember : literal ∈ clause)
    (sourceAtom : Variable)
    (literalSource : literal.atom = .inl sourceAtom) :
    ∃ sourceLiteral sourceLiteralIndex,
      (sourceLiteral, sourceLiteralIndex) ∈ source.zipIdx ∧
        sourceLiteral.atom = sourceAtom ∧
        literal.offset = sourceLiteral.offset := by
  rcases source with _ | ⟨first, rest⟩
  · simp only [clauseClauses, disjunctionGadget,
      forcePaddingFalse, padding,
      List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at clauseMember
    rcases clauseMember with
      (rfl | rfl | rfl) | rfl | rfl | rfl <;>
      simp_all [auxiliary, negate] <;>
      aesop
  · rcases rest with _ | ⟨second, rest⟩
    · simp only [clauseClauses, disjunctionGadget,
        forcePaddingFalse, padding,
        List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at clauseMember
      rcases clauseMember with
        (rfl | rfl | rfl) | rfl | rfl <;>
        simp_all [auxiliary, liftLiteral, negate] <;>
        aesop
    · rcases rest with _ | ⟨third, rest⟩
      · simp only [clauseClauses, disjunctionGadget,
          forcePaddingFalse, padding,
          List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false] at clauseMember
        rcases clauseMember with
          (rfl | rfl | rfl) | rfl <;>
          simp_all [auxiliary, liftLiteral, negate] <;>
          aesop
      · simp only [clauseClauses, disjunctionGadget,
          List.mem_cons, List.not_mem_nil,
          or_false] at clauseMember
        rcases clauseMember with rfl | rfl | rfl <;>
          simp_all [auxiliary, liftLiteral, negate] <;>
          aesop

end PeriodicOneInThree
end LeanTrominoes
