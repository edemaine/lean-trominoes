/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFOneDimensional
import LeanTrominoes.PeriodicCNFPlanarComponentNormalizationDegree

/-!
# One-dimensional normalized crossover clauses

Every variable in one physical crossover gadget has the same periodic site
shift.  Clause-anchor normalization removes that shift and leaves the
canonical crossover template with literal offset `(0, 0)`.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- Every normalized retained-halo crossover clause is one dimensional. -/
theorem normalizedScopedDrawingCrossoverClauses_isOneDimensional
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PeriodicCNF.IsOneDimensional
      ⟨normalizedScopedDrawingCrossoverClauses formula⟩ := by
  intro clause clauseMember literal literalMember
  rw [normalizedScopedDrawingCrossoverClauses_eq_normalized_sites]
    at clauseMember
  rcases List.mem_flatMap.mp clauseMember with
    ⟨crossing, _crossingMember, clauseMember⟩
  unfold normalizedCrossoverClausesAt at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨sourceClause, _sourceClauseMember, rfl⟩
  unfold normalizedCrossoverClause at literalMember
  rcases List.mem_map.mp literalMember with
    ⟨sourceLiteral, _sourceLiteralMember, rfl⟩
  rfl

end PeriodicOrthocrossing
end LeanTrominoes
