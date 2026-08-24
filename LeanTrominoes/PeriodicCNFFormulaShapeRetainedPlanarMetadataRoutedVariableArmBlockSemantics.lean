/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableDescriptorTemplateData
import LeanTrominoes.PeriodicGraph

/-! # Routed-variable descriptor blocks from ordered arms -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PlanarThreeSAT

/-- Presentation indices are irrelevant when a routed-variable descriptor
block depends only on the arm projected from each listed value. -/
theorem zipIdxCanonicalRoutedVariableBlocks_eq_armBlocks
    {Value : Type*} (values : List Value)
    (arm : Value → DuplicatorArm) :
    values.zipIdx.flatMap (fun tagged =>
        canonicalRoutedVariableDescriptorBlock (arm tagged.1) false) =
      (values.map arm).flatMap (fun selectedArm =>
        canonicalRoutedVariableDescriptorBlock selectedArm false) := by
  calc
    _ = values.flatMap (fun value =>
          canonicalRoutedVariableDescriptorBlock (arm value) false) :=
      PeriodicCNF.zipIdx_flatMap_fst
        (fun value =>
          canonicalRoutedVariableDescriptorBlock (arm value) false)
        values 0
    _ = _ := by rw [List.flatMap_map]

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
