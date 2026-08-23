/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableDescriptorData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableRelativeOffset

/-! # Canonical slices of routed-variable links -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- An active routed-variable arm never crosses into the next normalized
horizontal slice. -/
@[simp]
theorem routedVariableLinkNextSlice_eq_false
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (isLocal : source.incidenceGraph.IsLocal)
    (site : VariableRouteSite Variable)
    (link : EqualityLink (PlanarSATNode Variable))
    (linkMember : link ∈ routedVariableLinksAt source site) :
    routedVariableLinkNextSlice source link = false := by
  unfold routedVariableLinkNextSlice
  rw [routedVariableLink_relativeOffset_eq_zero
    source wellFormed isLocal site link linkMember]
  decide

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
