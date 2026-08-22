/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataClauseDescriptorMetadataData

/-! # Indexed metadata presentation of candidate clause descriptors -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

theorem metadataClauseDescriptorCandidates_eq_indexedMetadata
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    metadataClauseDescriptorCandidates source =
      indexedMetadataClauseDescriptors source := by
  unfold metadataClauseDescriptorCandidates normalizedClauses
    indexedMetadataClauseDescriptors
  rw [List.zipIdx_map, List.map_map]
  apply List.map_congr_left
  intro taggedMetadata _taggedMetadataMember
  rcases taggedMetadata with ⟨metadata, clauseIndex⟩
  rfl

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
