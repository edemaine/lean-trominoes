/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataClauseDescriptorMetadataIndexed
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataClauseDescriptorMetadataSemantics

/-! # Local-record presentation of candidate clause descriptors -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

/-- Candidate descriptors can be generated independently within each local
retained metadata record, in the original five-family presentation order. -/
theorem metadataClauseDescriptorCandidates_eq_mapped
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    metadataClauseDescriptorCandidates source =
      metadataMappedClauseDescriptors source :=
  (metadataClauseDescriptorCandidates_eq_indexedMetadata source).trans
    (indexedMetadataClauseDescriptors_eq_mapped source)

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
