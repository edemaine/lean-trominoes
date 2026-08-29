/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryDirectness

/-! # Route choices from one all-direct final clause query -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing

/-- Directness of one packed nonempty width-three clause query recovers a
successful route choice at each of its literal indices. -/
theorem retainedFinalCopiedClauseQueryOfLiterals_choices_of_allDirect
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex : Nat)
    (literals :
      PeriodicClause (WrappedPeriodicPlanarSATVariable Variable))
    (nonempty : literals ≠ [])
    (width : literals.length ≤ 3)
    (allDirect :
      (retainedFinalCopiedClauseQueryOfLiterals
        formula clauseIndex literals).AllDirect) :
    ∀ taggedLiteral ∈ literals.zipIdx,
      ∃ choice,
        retainedFinalDirectSourceRouteChoice?
            formula clauseIndex taggedLiteral.2 =
          some choice := by
  rcases literals with _ | ⟨first, rest⟩
  · contradiction
  rcases rest with _ | ⟨second, rest⟩
  · intro taggedLiteral taggedLiteralMember
    have taggedEq : taggedLiteral = (first, 0) := by
      simpa using taggedLiteralMember
    subst taggedLiteral
    apply (retainedFinalCopiedSourceDirectionQuery_isDirect_iff
      formula clauseIndex 0 first).mp
    change (retainedFinalCopiedSourceDirectionQuery
      formula clauseIndex 0 first).IsDirect at allDirect
    exact allDirect
  rcases rest with _ | ⟨third, rest⟩
  · intro taggedLiteral taggedLiteralMember
    have taggedEq :
        taggedLiteral = (first, 0) ∨
          taggedLiteral = (second, 1) := by
      simpa using taggedLiteralMember
    rcases taggedEq with rfl | rfl
    · apply (retainedFinalCopiedSourceDirectionQuery_isDirect_iff
        formula clauseIndex 0 first).mp
      change
        (retainedFinalCopiedSourceDirectionQuery
            formula clauseIndex 0 first).IsDirect ∧
          (retainedFinalCopiedSourceDirectionQuery
            formula clauseIndex 1 second).IsDirect at allDirect
      exact allDirect.1
    · apply (retainedFinalCopiedSourceDirectionQuery_isDirect_iff
        formula clauseIndex 1 second).mp
      change
        (retainedFinalCopiedSourceDirectionQuery
            formula clauseIndex 0 first).IsDirect ∧
          (retainedFinalCopiedSourceDirectionQuery
            formula clauseIndex 1 second).IsDirect at allDirect
      exact allDirect.2
  rcases rest with _ | ⟨fourth, rest⟩
  · intro taggedLiteral taggedLiteralMember
    have taggedEq :
        taggedLiteral = (first, 0) ∨
          taggedLiteral = (second, 1) ∨
            taggedLiteral = (third, 2) := by
      simpa using taggedLiteralMember
    rcases taggedEq with rfl | rfl | rfl
    · apply (retainedFinalCopiedSourceDirectionQuery_isDirect_iff
        formula clauseIndex 0 first).mp
      change
        (retainedFinalCopiedSourceDirectionQuery
            formula clauseIndex 0 first).IsDirect ∧
          (retainedFinalCopiedSourceDirectionQuery
              formula clauseIndex 1 second).IsDirect ∧
            (retainedFinalCopiedSourceDirectionQuery
              formula clauseIndex 2 third).IsDirect at allDirect
      exact allDirect.1
    · apply (retainedFinalCopiedSourceDirectionQuery_isDirect_iff
        formula clauseIndex 1 second).mp
      change
        (retainedFinalCopiedSourceDirectionQuery
            formula clauseIndex 0 first).IsDirect ∧
          (retainedFinalCopiedSourceDirectionQuery
              formula clauseIndex 1 second).IsDirect ∧
            (retainedFinalCopiedSourceDirectionQuery
              formula clauseIndex 2 third).IsDirect at allDirect
      exact allDirect.2.1
    · apply (retainedFinalCopiedSourceDirectionQuery_isDirect_iff
        formula clauseIndex 2 third).mp
      change
        (retainedFinalCopiedSourceDirectionQuery
            formula clauseIndex 0 first).IsDirect ∧
          (retainedFinalCopiedSourceDirectionQuery
              formula clauseIndex 1 second).IsDirect ∧
            (retainedFinalCopiedSourceDirectionQuery
              formula clauseIndex 2 third).IsDirect at allDirect
      exact allDirect.2.2
  · simp only [List.length_cons] at width
    omega

end PeriodicEightOccurrenceSplit
end LeanTrominoes
