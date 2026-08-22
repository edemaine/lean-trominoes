/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierClauseNormalizationAt
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierRouteDirections

/-! # Finite retained carrier descriptor templates -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT
open UnaryProgramClauseProfile

/-- Whether the second endpoint of a canonically normalized carrier link is
in the next horizontal period slice. -/
def carrierLinkNextSlice
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (link : EqualityLink CarrierNode) : Bool :=
  decide
    ((PeriodicEquality.normalizeLink
      (carrierWrappedVariableNormalization source) link).relativeOffset =
        ((1, 0) : Cell))

/-- The finite direction-aware descriptor of one carrier implication.  Its
only inputs are the carrier axis, the normalized relative-slice bit, and the
choice of forward or backward implication. -/
def carrierClauseDescriptor
    (horizontal nextSlice forward : Bool) :
    FormulaShapeDirectionOrdering.Token :=
  match forward with
  | true =>
      .clause (.binary
        ⟨false, true⟩ (carrierLensRouteFirstDirection horizontal 0 0)
        ⟨nextSlice, false⟩ (carrierLensRouteFirstDirection horizontal 0 1))
  | false =>
      .clause (.binary
        ⟨false, false⟩ (carrierLensRouteFirstDirection horizontal 1 0)
        ⟨nextSlice, true⟩ (carrierLensRouteFirstDirection horizontal 1 1))

/-- Fixed two-token block determined by one retained carrier link's two
finite bits. -/
def canonicalCarrierLinkDescriptorBlock
    (horizontal nextSlice : Bool) :
    List FormulaShapeDirectionOrdering.Token :=
  [carrierClauseDescriptor horizontal nextSlice true,
    carrierClauseDescriptor horizontal nextSlice false]

@[simp] theorem canonicalCarrierLinkDescriptorBlock_length
    (horizontal nextSlice : Bool) :
    (canonicalCarrierLinkDescriptorBlock horizontal nextSlice).length = 2 :=
  rfl

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
