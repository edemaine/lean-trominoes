/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataClauseDescriptorCandidateSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataClauseDescriptorIndexed

/-! # Representative presentation of retained metadata clause descriptors -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

/-- The public clause-descriptor prefix is exactly the list of first-source
candidate descriptors in last-representative deduplication order. -/
theorem clauseDescriptors_eq_representativeClauseDescriptors
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    clauseDescriptors source = representativeClauseDescriptors source :=
  (clauseDescriptors_eq_rawIndexedClauseDescriptors source).trans
    (rawIndexedClauseDescriptors_eq_representativeClauseDescriptors source)

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
