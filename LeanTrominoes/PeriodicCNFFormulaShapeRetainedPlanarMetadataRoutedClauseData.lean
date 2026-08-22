/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableFamilySemantics

/-! # Explicit retained routed-clause metadata -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Exact metadata for the source clause represented at one neighboring
clause-route site. -/
def routedClauseMetadataAt
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (site : ClauseRouteSite) : DrawingPlanarSATClauseMetadata Variable :=
  ⟨(routedClauseAt source site).rename planarSATExternalVariableMap,
    .routedClause site⟩

@[simp] theorem drawingPlanarSATRoutedClauseMetadata_eq_map
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    drawingPlanarSATRoutedClauseMetadata source =
      (drawingClauseRouteSites source).map
        (routedClauseMetadataAt source) := by
  rfl

/-- The routed source-clause descriptor family is the presentation-order
map of one descriptor per represented clause site. -/
theorem routedClauseMetadataClauseDescriptors_eq_map_sites
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    routedClauseMetadataClauseDescriptors source =
      (drawingClauseRouteSites source).map fun site =>
        metadataClauseDescriptor source
          (routedClauseMetadataAt source site) := by
  unfold routedClauseMetadataClauseDescriptors
  rw [drawingPlanarSATRoutedClauseMetadata_eq_map]
  rw [List.map_map]
  rfl

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
