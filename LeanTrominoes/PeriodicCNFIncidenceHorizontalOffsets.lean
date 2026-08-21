/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTransition
import LeanTrominoes.PeriodicGraph

/-! # Horizontal normalized offsets of forward-local CNF incidences -/

namespace LeanTrominoes
namespace PeriodicCNF

theorem incidenceEdge_offset_zero_right_or_left_of_forward
    {Variable : Type*} (clauseIndex : Nat)
    (clause : PeriodicClause Variable)
    (literal : PeriodicLiteral Variable)
    (literalMember : literal ∈ clause)
    (forward : ∀ item ∈ clause, item.IsForwardLocal) :
    (incidenceEdge clauseIndex (clauseAnchor clause) literal).offset =
        (0, 0) ∨
      (incidenceEdge clauseIndex (clauseAnchor clause) literal).offset =
        (1, 0) ∨
      (incidenceEdge clauseIndex (clauseAnchor clause) literal).offset =
        (-1, 0) := by
  cases clause with
  | nil => simp at literalMember
  | cons first rest =>
      have firstForward := forward first (by simp)
      have literalForward := forward literal literalMember
      rcases firstForward with firstCurrent | firstNext <;>
        rcases literalForward with literalCurrent | literalNext
      all_goals simp_all [incidenceEdge, clauseAnchor, Cell.sub]

end PeriodicCNF
end LeanTrominoes
