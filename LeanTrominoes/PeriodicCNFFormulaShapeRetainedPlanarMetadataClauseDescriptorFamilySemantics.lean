/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataClauseDescriptorFamilies
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataClauseDescriptorLocalSemantics

/-! # Family semantics of retained metadata descriptor candidates -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

theorem metadataClauseDescriptorCandidates_eq_families
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    metadataClauseDescriptorCandidates source =
      familyMetadataClauseDescriptors source :=
  (metadataClauseDescriptorCandidates_eq_mapped source).trans
    (metadataMappedClauseDescriptors_eq_families source)

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
