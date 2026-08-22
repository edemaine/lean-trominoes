/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableDescriptorBlocks

/-! # Explicit local routed-variable clauses and metadata -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- The forward or backward implication clause of one active routed-variable
equality arm, embedded into the combined planar-SAT variable type. -/
def routedVariableClauseAt
    {Variable : Type}
    (link : EqualityLink (PlanarSATNode Variable))
    (forward : Bool) : EmbeddedClause (PlanarSATVariable Variable) :=
  let clause : EmbeddedClause (PlanarSATNode Variable) :=
    if forward then
      ⟨link.positions.forward,
        [(link.first, true), (link.second, false)]⟩
    else
      ⟨link.positions.backward,
        [(link.first, false), (link.second, true)]⟩
  clause.rename planarSATExternalVariableMap

/-- Exact local metadata for one implication of an active routed-variable
equality arm. -/
def routedVariableClauseMetadataAt
    {Variable : Type}
    (site : VariableRouteSite Variable)
    (armIndex : Nat)
    (arm : DuplicatorArm)
    (link : EqualityLink (PlanarSATNode Variable))
    (forward : Bool) : DrawingPlanarSATClauseMetadata Variable :=
  ⟨routedVariableClauseAt link forward,
    .routedVariable site armIndex arm link
      (if forward then 0 else 1)⟩

@[simp] theorem drawingPlanarSATRoutedVariableFormulaAt_eq_pair
    {Variable : Type}
    (link : EqualityLink (PlanarSATNode Variable)) :
    drawingPlanarSATRoutedVariableFormulaAt link =
      [routedVariableClauseAt link true,
        routedVariableClauseAt link false] := by
  simp [drawingPlanarSATRoutedVariableFormulaAt,
    equalityInstance, routedVariableClauseAt]

@[simp] theorem drawingPlanarSATRoutedVariableClauseMetadataFor_eq_pair
    {Variable : Type}
    (site : VariableRouteSite Variable)
    (armIndex : Nat)
    (arm : DuplicatorArm)
    (link : EqualityLink (PlanarSATNode Variable)) :
    drawingPlanarSATRoutedVariableClauseMetadataFor
        site armIndex arm link =
      [routedVariableClauseMetadataAt
          site armIndex arm link true,
        routedVariableClauseMetadataAt
          site armIndex arm link false] := by
  simp [drawingPlanarSATRoutedVariableClauseMetadataFor,
    routedVariableClauseMetadataAt]

/-- The local active-arm descriptor block is explicitly the forward
descriptor followed by the backward descriptor. -/
theorem routedVariableLinkClauseDescriptors_eq_pair
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (site : VariableRouteSite Variable)
    (armIndex : Nat)
    (arm : DuplicatorArm)
    (link : EqualityLink (PlanarSATNode Variable)) :
    routedVariableLinkClauseDescriptors
        source site armIndex arm link =
      [metadataClauseDescriptor source
          (routedVariableClauseMetadataAt
            site armIndex arm link true),
        metadataClauseDescriptor source
          (routedVariableClauseMetadataAt
            site armIndex arm link false)] := by
  simp [routedVariableLinkClauseDescriptors]

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
