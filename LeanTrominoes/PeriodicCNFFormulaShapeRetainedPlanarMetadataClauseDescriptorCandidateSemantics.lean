/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRepresentativeClauseDescriptor
import LeanTrominoes.ListMapZipIdxCongr

/-! # Semantics of candidate retained metadata clause descriptors -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- The indexed raw descriptors select the first source candidate for each
clause, while retaining the last-occurrence-preserving deduplication order. -/
theorem rawIndexedClauseDescriptors_eq_representativeClauseDescriptors
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    rawIndexedClauseDescriptors source =
      representativeClauseDescriptors source := by
  simp only [rawIndexedClauseDescriptors,
    representativeClauseDescriptors]
  apply List.map_zipIdx_eq_map_of_mem
  intro taggedClause taggedClauseMember
  have clauseLookup :
      (deduplicatedClauses source)[taggedClause.2]? =
        some taggedClause.1 :=
    (List.mem_zipIdx_iff_getElem?).mp taggedClauseMember
  exact rawIndexedClauseDescriptor_eq_representative_of_lookup
    source taggedClause clauseLookup

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
