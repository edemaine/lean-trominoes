/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFOneDimensional
import LeanTrominoes.PeriodicCNFPlanarClauseNormalizationDegree

/-!
# One-dimensional normalized routed source clauses

Anchor normalization removes the common explicit translate from every
routed original clause.  Its remaining terminal literals all have offset
zero, independently of the source geometry.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- Every anchor-normalized routed original-clause literal has zero vertical
offset. -/
theorem normalizedRoutedClauseClauses_isOneDimensional
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PeriodicCNF.IsOneDimensional
      ⟨normalizedRoutedClauseClauses formula⟩ := by
  intro clause clauseMember literal literalMember
  obtain ⟨site, _siteMember, clauseEq⟩ :=
    normalizedRoutedClause_mem_witness formula clauseMember
  rw [clauseEq] at literalMember
  simp only [List.mem_map] at literalMember
  obtain ⟨taggedIncidence, _taggedIncidenceMember, rfl⟩ := literalMember
  rfl

end PeriodicOrthocrossing
end LeanTrominoes
