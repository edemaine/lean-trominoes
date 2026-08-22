/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBendDescriptorSemanticsAt

/-! # Complete retained bend descriptor-family semantics -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- One routed bend contributes exactly its canonical finite two-token
descriptor block. -/
theorem bendClauseDescriptors_eq_canonicalBlock
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routeBend : RouteBend) :
    bendClauseDescriptors source routeBend =
      canonicalBendDescriptorBlock
        routeBend.incomingPort routeBend.outgoingPort
        (bendLinkNextSlice source routeBend) := by
  rw [bendClauseDescriptors_eq_pair]
  unfold canonicalBendDescriptorBlock
  rw [metadataClauseDescriptor_bendClauseMetadataAt_eq
      source routeBend true,
    metadataClauseDescriptor_bendClauseMetadataAt_eq
      source routeBend false]

/-- The complete retained bend family is a finite two-token expansion of
the deduplicated route-bend scan. -/
theorem bendMetadataClauseDescriptors_eq_canonicalBlocks
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    bendMetadataClauseDescriptors source =
      (drawingRouteBends source.incidenceGraph).dedup.flatMap
        fun routeBend =>
          canonicalBendDescriptorBlock
            routeBend.incomingPort routeBend.outgoingPort
            (bendLinkNextSlice source routeBend) := by
  rw [bendMetadataClauseDescriptors_eq_flatMap_bendBlocks]
  apply List.flatMap_congr
  intro routeBend _
  exact bendClauseDescriptors_eq_canonicalBlock source routeBend

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
