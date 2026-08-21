/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTransition
import LeanTrominoes.PeriodicThreeCNF

/-! # Forward-locality of periodic width-three conversion -/

namespace LeanTrominoes
namespace PeriodicThreeCNF

theorem supported_isForwardLocal
    {Variable : Type*}
    (source : PeriodicClause Variable)
    (sourceForward :
      ∀ literal ∈ source, literal.IsForwardLocal)
    (literal : PeriodicLiteral (ThreeCNFVariable Variable))
    (supported : Supported source literal) :
    literal.IsForwardLocal := by
  rcases supported with
    ⟨original, originalMember, rfl⟩ |
      ⟨suffix, value, rfl⟩
  · simpa [liftLiteral, PeriodicLiteral.IsForwardLocal] using
      sourceForward original originalMember
  · cases source with
    | nil => simp [auxiliary, anchor, PeriodicLiteral.IsForwardLocal]
    | cons first rest =>
        have firstForward := sourceForward first (by simp)
        rcases firstForward with current | next
        all_goals simp_all [auxiliary, anchor,
          PeriodicLiteral.IsForwardLocal]

theorem clauseClauses_areForwardLocal
    {Variable : Type*}
    (source : PeriodicClause Variable)
    (sourceForward :
      ∀ literal ∈ source, literal.IsForwardLocal) :
    ∀ clause ∈ clauseClauses source,
      ∀ literal ∈ clause, literal.IsForwardLocal := by
  intro clause clauseMember literal literalMember
  exact supported_isForwardLocal source sourceForward literal
    (clauseClauses_supported source clause clauseMember
      literal literalMember)

/-- Width-three conversion preserves the current/next-slice fragment. -/
theorem formula_isForwardLocal
    {Variable : Type*} {source : PeriodicCNF Variable}
    (sourceForward : source.IsForwardLocal) :
    (formula source).IsForwardLocal := by
  intro clause clauseMember literal literalMember
  simp only [formula, List.mem_flatMap] at clauseMember
  rcases clauseMember with
    ⟨sourceClause, sourceClauseMember, clauseMember⟩
  exact clauseClauses_areForwardLocal sourceClause
    (sourceForward sourceClause sourceClauseMember)
    clause clauseMember literal literalMember

end PeriodicThreeCNF
end LeanTrominoes
