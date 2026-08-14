/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFOneDimensional

/-!
# List operations on one-dimensional periodic CNF

One-dimensionality is a pointwise clause property, so it is preserved by
concatenating clause families and by removing duplicate clauses.
-/

namespace LeanTrominoes
namespace PeriodicCNF

/-- Concatenating two one-dimensional clause lists preserves
one-dimensionality. -/
theorem IsOneDimensional.append
    {Variable : Type*}
    {first second : List (PeriodicClause Variable)}
    (firstHorizontal : IsOneDimensional ⟨first⟩)
    (secondHorizontal : IsOneDimensional ⟨second⟩) :
    IsOneDimensional ⟨first ++ second⟩ := by
  intro clause clauseMember literal literalMember
  rcases List.mem_append.mp clauseMember with
    clauseMember | clauseMember
  · exact firstHorizontal clause clauseMember literal literalMember
  · exact secondHorizontal clause clauseMember literal literalMember

/-- Removing duplicate clauses preserves one-dimensionality. -/
theorem IsOneDimensional.dedup
    {Variable : Type*} [DecidableEq Variable]
    {clauses : List (PeriodicClause Variable)}
    (horizontal : IsOneDimensional ⟨clauses⟩) :
    IsOneDimensional ⟨clauses.dedup⟩ := by
  intro clause clauseMember literal literalMember
  exact horizontal clause (List.mem_dedup.mp clauseMember)
    literal literalMember

end PeriodicCNF
end LeanTrominoes
