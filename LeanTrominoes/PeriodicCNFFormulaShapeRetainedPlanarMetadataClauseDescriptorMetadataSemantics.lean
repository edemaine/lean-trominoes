/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListMapZipIdxCongr
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataLocalClauseDescriptor

/-! # Local metadata semantics of candidate clause descriptors -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

theorem indexedMetadataClauseDescriptors_eq_mapped
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    indexedMetadataClauseDescriptors source =
      metadataMappedClauseDescriptors source := by
  simp only [indexedMetadataClauseDescriptors,
    metadataMappedClauseDescriptors]
  apply List.map_zipIdx_eq_map_of_mem
  intro taggedMetadata taggedMetadataMember
  have metadataLookup :
      (retainedDrawingPlanarSATClauseMetadata source)[taggedMetadata.2]? =
        some taggedMetadata.1 :=
    (List.mem_zipIdx_iff_getElem?).mp taggedMetadataMember
  exact indexedMetadataClauseDescriptor_eq_local_of_lookup
    source taggedMetadata metadataLookup

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
