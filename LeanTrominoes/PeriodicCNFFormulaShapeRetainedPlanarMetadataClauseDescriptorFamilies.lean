/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataClauseDescriptorFamilyData

/-! # Exact family decomposition of retained metadata clause descriptors -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

theorem metadataMappedClauseDescriptors_eq_families
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    metadataMappedClauseDescriptors source =
      familyMetadataClauseDescriptors source := by
  unfold metadataMappedClauseDescriptors
    retainedDrawingPlanarSATClauseMetadata
    familyMetadataClauseDescriptors
    crossoverMetadataClauseDescriptors
    carrierMetadataClauseDescriptors
    bendMetadataClauseDescriptors
    routedClauseMetadataClauseDescriptors
    routedVariableMetadataClauseDescriptors
  simp only [List.map_append]

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
