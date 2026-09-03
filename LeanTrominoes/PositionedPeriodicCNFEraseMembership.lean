/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarThreeSATThreePositioned
import Mathlib.Data.List.Enum

/-! # Membership in erased positioned formulas -/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

/-- The literals of a zip-indexed positioned clause belong to the erased
formula. -/
theorem literals_mem_erase_of_mem_zipIdx
    {Variable : Type*}
    {source : PositionedPeriodicCNF Variable}
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ source.clauses.zipIdx) :
    clause.literals ∈ source.erase.clauses := by
  exact List.mem_map.mpr
    ⟨clause, List.fst_mem_of_mem_zipIdx clauseMember, rfl⟩

end PositionedPeriodicCNF
end LeanTrominoes
