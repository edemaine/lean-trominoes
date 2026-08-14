/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFOneDimensional

/-!
# Mapping one-dimensional periodic CNF clauses

Mapping every literal of every clause preserves one-dimensionality whenever
the map preserves each literal's vertical offset.  This small interface keeps
later atom embeddings from repeatedly elaborating nested list-membership
proofs.
-/

namespace LeanTrominoes
namespace PeriodicCNF

/-- A clausewise literal map that preserves vertical offsets preserves the
one-dimensional fragment. -/
theorem IsOneDimensional.mapLiterals
    {Source Target : Type*}
    (clauses : List (PeriodicClause Source))
    (mapLiteral : PeriodicLiteral Source → PeriodicLiteral Target)
    (verticalPreserved :
      ∀ literal, (mapLiteral literal).offset.2 = literal.offset.2)
    (horizontal : IsOneDimensional ⟨clauses⟩) :
    IsOneDimensional
      ⟨clauses.map fun clause => clause.map mapLiteral⟩ := by
  intro targetClause targetClauseMember targetLiteral targetLiteralMember
  rcases List.mem_map.mp targetClauseMember with
    ⟨sourceClause, sourceClauseMember, rfl⟩
  rcases List.mem_map.mp targetLiteralMember with
    ⟨sourceLiteral, sourceLiteralMember, rfl⟩
  rw [verticalPreserved]
  exact horizontal sourceClause sourceClauseMember
    sourceLiteral sourceLiteralMember

end PeriodicCNF
end LeanTrominoes
