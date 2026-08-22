/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedClauseDescriptorSemanticsAt

/-! # Complete routed source-clause descriptor-family semantics -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- The complete routed source-clause family is the presentation-order map
of the canonical finite token at every represented neighboring clause site. -/
theorem routedClauseMetadataClauseDescriptors_eq_canonicalDescriptors
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    routedClauseMetadataClauseDescriptors source =
      (drawingClauseRouteSites source).map
        (canonicalRoutedClauseDescriptor source) := by
  rw [routedClauseMetadataClauseDescriptors_eq_map_sites]
  apply List.map_congr_left
  intro site _
  exact metadataClauseDescriptor_routedClauseMetadataAt_eq source site

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
