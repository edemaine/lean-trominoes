/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableArmBlockSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableSiteArmDescriptorData

/-! # Site-major routed-variable descriptor expansion -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PlanarThreeSAT

/-- Expanding canonical current-slice link blocks in nested site/`zipIdx`
order is exactly the descriptor expansion of the corresponding site-arm
scan. -/
theorem routedVariableCanonicalBlocks_eq_siteArmDescriptorStream
    {Site Link : Type*}
    (sites : List Site) (links : Site → List Link)
    (arm : Link → DuplicatorArm) :
    sites.flatMap (fun site =>
        (links site).zipIdx.flatMap fun taggedLink =>
          canonicalRoutedVariableDescriptorBlock
            (arm taggedLink.1) false) =
      routedVariableSiteArmDescriptorStream
        (sites.map fun site => (links site).map arm) := by
  unfold routedVariableSiteArmDescriptorStream
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro site _siteMember
  exact zipIdxCanonicalRoutedVariableBlocks_eq_armBlocks
    (links site) arm

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
