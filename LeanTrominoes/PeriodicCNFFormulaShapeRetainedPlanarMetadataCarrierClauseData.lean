/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierDescriptorBlocks

/-! # Explicit local carrier clauses and metadata -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- The forward or backward implication clause of one carrier equality link,
embedded into the combined planar-SAT variable type. -/
def carrierClauseAt
    {Variable : Type}
    (link : EqualityLink CarrierNode)
    (forward : Bool) : EmbeddedClause (PlanarSATVariable Variable) :=
  let clause : EmbeddedClause CarrierNode :=
    if forward then
      ⟨link.positions.forward,
        [(link.first, true), (link.second, false)]⟩
    else
      ⟨link.positions.backward,
        [(link.first, false), (link.second, true)]⟩
  (clause.rename fun node =>
      (Sum.inl node :
        Sum CarrierNode (CrossingRecord × CrossoverInternal))).rename
    (@planarSATCoreVariableMap Variable)

/-- Exact local metadata for one of a carrier link's two implications. -/
def carrierClauseMetadataAt
    {Variable : Type}
    (link : EqualityLink CarrierNode)
    (forward : Bool) : DrawingPlanarSATClauseMetadata Variable :=
  ⟨carrierClauseAt link forward,
    .carrier link (if forward then 0 else 1)⟩

@[simp] theorem drawingPlanarSATCarrierFormulaAt_eq_pair
    {Variable : Type}
    (link : EqualityLink CarrierNode) :
    drawingPlanarSATCarrierFormulaAt (Variable := Variable) link =
      [carrierClauseAt link true, carrierClauseAt link false] := by
  simp [drawingPlanarSATCarrierFormulaAt, equalityInstance,
    carrierClauseAt]

@[simp] theorem drawingPlanarSATCarrierClauseMetadataFor_eq_pair
    {Variable : Type}
    (link : EqualityLink CarrierNode) :
    drawingPlanarSATCarrierClauseMetadataFor
        (Variable := Variable) link =
      [carrierClauseMetadataAt link true,
        carrierClauseMetadataAt link false] := by
  simp [drawingPlanarSATCarrierClauseMetadataFor,
    carrierClauseMetadataAt]

/-- The local descriptor block is explicitly the forward descriptor followed
by the backward descriptor. -/
theorem carrierLinkClauseDescriptors_eq_pair
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (link : EqualityLink CarrierNode) :
    carrierLinkClauseDescriptors source link =
      [metadataClauseDescriptor source
          (carrierClauseMetadataAt link true),
        metadataClauseDescriptor source
          (carrierClauseMetadataAt link false)] := by
  simp [carrierLinkClauseDescriptors]

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
