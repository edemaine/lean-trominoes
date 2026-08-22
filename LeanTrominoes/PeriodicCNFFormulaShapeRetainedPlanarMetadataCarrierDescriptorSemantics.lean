/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierDescriptorData

/-! # Semantics of finite retained carrier descriptor templates -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT
open UnaryProgramClauseProfile

/-- The two literal profiles of a normalized carrier implication are fixed by
its implication polarity and the normalized link's relative-slice bit. -/
theorem normalizedCarrierClause_literalProfiles_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (link : EqualityLink CarrierNode)
    (forward : Bool) :
    (normalizedClause source
        (carrierClauseMetadataAt link forward)).map
        FormulaShapeDirectionOrdering.literalProfile =
      if forward then
        [(⟨false, true⟩ : LiteralProfile),
          ⟨carrierLinkNextSlice source link, false⟩]
      else
        [(⟨false, false⟩ : LiteralProfile),
          ⟨carrierLinkNextSlice source link, true⟩] := by
  rw [normalizedClause_carrierClauseMetadataAt_eq]
  cases forward <;>
    simp [PeriodicEquality.normalizedClause,
      carrierLinkNextSlice,
      FormulaShapeDirectionOrdering.literalProfile]

/-- Every selected retained carrier implication has exactly its finite
two-bit equality-lens descriptor. -/
theorem metadataClauseDescriptor_carrierClauseMetadataAt_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal)
    (link : EqualityLink CarrierNode)
    (linkMember :
      link ∈ retainedDrawingCompleteCarrierLinks source.incidenceGraph)
    (forward : Bool) :
    metadataClauseDescriptor source
        (carrierClauseMetadataAt link forward) =
      carrierClauseDescriptor link.first.isHorizontal
        (carrierLinkNextSlice source link) forward := by
  cases forward
  all_goals
    unfold metadataClauseDescriptor
    rw [normalizedClause_carrierClauseMetadataAt_eq]
    simp [carrierClauseMetadataAt,
      DrawingPlanarSATClauseSource.localClauseIndex,
      FormulaShapeDirectionOrdering.DirectedClauseProfile.ofClause,
      FormulaShapeDirectionOrdering.DirectedClauseProfile.ofList,
      FormulaShapeDirectionOrdering.annotatedLiterals,
      carrierClauseDescriptor,
      PeriodicEquality.normalizedClause,
      carrierLinkNextSlice,
      FormulaShapeDirectionOrdering.literalProfile,
      carrier_routeFirstDirection_eq source wellFormed degree isLocal
        link linkMember]

/-- One retained carrier link contributes exactly its canonical finite
two-token descriptor block. -/
theorem carrierLinkClauseDescriptors_eq_canonicalBlock
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal)
    (link : EqualityLink CarrierNode)
    (linkMember :
      link ∈ retainedDrawingCompleteCarrierLinks source.incidenceGraph) :
    carrierLinkClauseDescriptors source link =
      canonicalCarrierLinkDescriptorBlock link.first.isHorizontal
        (carrierLinkNextSlice source link) := by
  rw [carrierLinkClauseDescriptors_eq_pair]
  unfold canonicalCarrierLinkDescriptorBlock
  rw [metadataClauseDescriptor_carrierClauseMetadataAt_eq
      source wellFormed degree isLocal link linkMember true,
    metadataClauseDescriptor_carrierClauseMetadataAt_eq
      source wellFormed degree isLocal link linkMember false]

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
