import LeanTrominoes.PeriodicOneInThreeNoUnits

/-!
# Source scopes of unit-elimination auxiliary incidences

Every auxiliary literal emitted by one unit-elimination clause block carries
that block's source clause and presentation index, and is placed at the
source clause's logical anchor.  These facts identify its local geometric
endpoint with its canonical periodic endpoint.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreeNoUnits

/-- An auxiliary occurring in a generated unit-elimination block has exactly
the block's scope and anchor offset. -/
theorem auxiliary_scope_offset_of_mem_clauseClauses
    {Variable : Type*}
    (clauseIndex : Nat)
    (source : PeriodicClause Variable)
    {clause :
      PeriodicClause (OneInThreeNoUnitVariable Variable)}
    (clauseMember :
      clause ∈ clauseClauses clauseIndex source)
    {literal :
      PeriodicLiteral (OneInThreeNoUnitVariable Variable)}
    (literalMember : literal ∈ clause)
    (auxiliary :
      (Nat × PeriodicClause Variable) × OneInThreeNoUnitAux)
    (literalAuxiliary : literal.atom = .inr auxiliary) :
    auxiliary.1 = (clauseIndex, source) ∧
      literal.offset = PeriodicOneInThree.anchor source := by
  rcases source with _ | ⟨first, rest⟩
  · simp only [clauseClauses, List.mem_cons,
      List.not_mem_nil, or_false] at clauseMember
    rcases clauseMember with rfl | rfl | rfl <;>
      simp_all [PeriodicOneInThreeNoUnits.auxiliary] <;>
      aesop
  · rcases rest with _ | ⟨second, rest⟩
    · simp only [clauseClauses, List.mem_cons,
        List.not_mem_nil, or_false] at clauseMember
      rcases clauseMember with rfl | rfl <;>
        simp_all [PeriodicOneInThreeNoUnits.auxiliary,
          liftLiteral, PeriodicOneInThree.negate] <;>
        aesop
    · simp only [clauseClauses, List.mem_singleton] at clauseMember
      subst clause
      simp only [List.mem_map, List.mem_cons] at literalMember
      rcases literalMember with ⟨term, _, termEqual⟩
      subst literal
      simp [liftLiteral] at literalAuxiliary

end PeriodicOneInThreeNoUnits
end LeanTrominoes
