/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeDirectionOrderingTokenData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableRouteDirectionData

/-! # Static retained routed-variable descriptor templates -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PlanarThreeSAT

/-- The finite direction-aware descriptor of one active routed-variable
implication. -/
def routedVariableClauseDescriptor
    (arm : DuplicatorArm)
    (nextSlice forward : Bool) :
    FormulaShapeDirectionOrdering.Token :=
  match forward with
  | true =>
      .clause (.binary
        ⟨false, true⟩ (routedVariableRouteFirstDirection arm 0 0)
        ⟨nextSlice, false⟩
          (routedVariableRouteFirstDirection arm 0 1))
  | false =>
      .clause (.binary
        ⟨false, false⟩ (routedVariableRouteFirstDirection arm 1 0)
        ⟨nextSlice, true⟩
          (routedVariableRouteFirstDirection arm 1 1))

/-- Fixed two-token block determined by one active routed-variable arm and
its normalized relative-slice bit. -/
def canonicalRoutedVariableDescriptorBlock
    (arm : DuplicatorArm)
    (nextSlice : Bool) :
    List FormulaShapeDirectionOrdering.Token :=
  [routedVariableClauseDescriptor arm nextSlice true,
    routedVariableClauseDescriptor arm nextSlice false]

@[simp] theorem canonicalRoutedVariableDescriptorBlock_length
    (arm : DuplicatorArm)
    (nextSlice : Bool) :
    (canonicalRoutedVariableDescriptorBlock arm nextSlice).length = 2 :=
  rfl

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
