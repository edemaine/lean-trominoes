/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBendLiteralProfiles

/-! # Pointwise semantics of finite retained bend descriptors -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Every routed-bend implication has exactly its finite corner-table
descriptor. -/
theorem metadataClauseDescriptor_bendClauseMetadataAt_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routeBend : RouteBend)
    (forward : Bool) :
    metadataClauseDescriptor source
        (bendClauseMetadataAt source.incidenceGraph routeBend forward) =
      bendClauseDescriptor routeBend.incomingPort routeBend.outgoingPort
        (bendLinkNextSlice source routeBend) forward := by
  cases forward
  all_goals
    unfold metadataClauseDescriptor
    rw [normalizedClause_bendClauseMetadataAt_eq]
    simp [bendClauseMetadataAt,
      DrawingPlanarSATClauseSource.localClauseIndex,
      FormulaShapeDirectionOrdering.DirectedClauseProfile.ofClause,
      FormulaShapeDirectionOrdering.DirectedClauseProfile.ofList,
      FormulaShapeDirectionOrdering.annotatedLiterals,
      bendClauseDescriptor,
      PeriodicEquality.normalizedClause,
      bendLinkNextSlice, carrierLinkNextSlice,
      FormulaShapeDirectionOrdering.literalProfile,
      bend_routeFirstDirection_eq source routeBend]

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
