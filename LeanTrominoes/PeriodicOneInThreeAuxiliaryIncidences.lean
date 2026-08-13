/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThree

/-!
# Source scopes of Figure 9 auxiliary incidences

Every auxiliary literal emitted by one Figure 9 clause block carries that
block's source clause and presentation index, and is placed at the source
clause's logical anchor.  These facts identify its local geometric endpoint
with its canonical periodic endpoint.
-/

namespace LeanTrominoes
namespace PeriodicOneInThree

/-- An auxiliary occurring in a generated Figure 9 block has exactly the
block's scope and anchor offset. -/
theorem auxiliary_scope_offset_of_mem_clauseClauses
    {Variable : Type*}
    (clauseIndex : Nat)
    (source : PeriodicClause Variable)
    {clause :
      PeriodicClause (OneInThreeVariable Variable)}
    (clauseMember :
      clause ∈ clauseClauses clauseIndex source)
    {literal :
      PeriodicLiteral (OneInThreeVariable Variable)}
    (literalMember : literal ∈ clause)
    (auxiliary :
      (Nat × PeriodicClause Variable) × OneInThreeAux)
    (literalAuxiliary : literal.atom = .inr auxiliary) :
    auxiliary.1 = (clauseIndex, source) ∧
      literal.offset = anchor source := by
  rcases source with _ | ⟨first, rest⟩
  · simp only [clauseClauses, disjunctionGadget,
      forcePaddingFalse, padding,
      List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at clauseMember
    rcases clauseMember with
      (rfl | rfl | rfl) | rfl | rfl | rfl <;>
      simp_all [PeriodicOneInThree.auxiliary, negate] <;>
      aesop
  · rcases rest with _ | ⟨second, rest⟩
    · simp only [clauseClauses, disjunctionGadget,
        forcePaddingFalse, padding,
        List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at clauseMember
      rcases clauseMember with
        (rfl | rfl | rfl) | rfl | rfl <;>
        simp_all [PeriodicOneInThree.auxiliary,
          liftLiteral, negate] <;>
        aesop
    · rcases rest with _ | ⟨third, rest⟩
      · simp only [clauseClauses, disjunctionGadget,
          forcePaddingFalse, padding,
          List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false] at clauseMember
        rcases clauseMember with
          (rfl | rfl | rfl) | rfl <;>
          simp_all [PeriodicOneInThree.auxiliary,
            liftLiteral, negate] <;>
          aesop
      · simp only [clauseClauses, disjunctionGadget,
          List.mem_cons, List.not_mem_nil,
          or_false] at clauseMember
        rcases clauseMember with rfl | rfl | rfl <;>
          simp_all [PeriodicOneInThree.auxiliary,
            liftLiteral, negate] <;>
          aesop

end PeriodicOneInThree
end LeanTrominoes
