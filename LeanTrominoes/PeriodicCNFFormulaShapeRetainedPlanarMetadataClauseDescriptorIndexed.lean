/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataClauseDescriptorCandidateData

/-! # Indexed presentation of retained metadata clause descriptors -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

theorem clauseDescriptors_eq_rawIndexedClauseDescriptors
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    clauseDescriptors source = rawIndexedClauseDescriptors source := by
  unfold clauseDescriptors positionedSource rawIndexedClauseDescriptors
  rw [List.zipIdx_map, List.map_map]
  apply List.map_congr_left
  intro taggedClause _taggedClauseMember
  rcases taggedClause with ⟨clause, clauseIndex⟩
  rfl

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
