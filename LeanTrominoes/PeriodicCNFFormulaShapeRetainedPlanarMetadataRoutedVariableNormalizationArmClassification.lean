/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableNormalizationClassification

/-! # Arm classification of normalized routed-variable links -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Read the physical duplicator arm from the first terminal prototype of a
wrapped normalized routed-variable link. -/
def wrappedNormalizedRoutedVariableLinkArm
    {Variable : Type}
    (link : PeriodicEquality.NormalizedLink
      (WrappedPeriodicPlanarSATVariable Variable)) : DuplicatorArm :=
  match link.first.original with
  | .terminal indexed endpoint =>
      (SegmentTerminal.mk indexed (0, 0) endpoint).duplicatorArm
  | _ => .right

/-- Wrapping, periodic normalization, and retained gauging preserve the
active source link's physical duplicator arm. -/
@[simp] theorem wrappedNormalizedRoutedVariableLinkArm_normalizeLink
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (link : EqualityLink (PlanarSATNode Variable))
    (linkMember : link ∈ drawingRoutedVariableLinks source) :
    wrappedNormalizedRoutedVariableLinkArm
        (PeriodicEquality.normalizeLink
          (externalWrappedVariableNormalization source) link) =
      link.first.duplicatorArm := by
  rcases drawingRoutedVariableLink_witness source linkMember with
    ⟨site, occurrence, _occurrenceMember, _siteEq,
      firstEq, _secondEq⟩
  unfold wrappedNormalizedRoutedVariableLinkArm
    PeriodicEquality.normalizeLink
  rw [firstEq]
  rfl

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
