/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBendDescriptorBlocks
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierClauseData

/-! # Explicit local bend clauses and metadata -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Exact local metadata for one implication of a routed bend's equality
link. -/
def bendClauseMetadataAt
    {Variable Vertex : Type} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (routeBend : RouteBend)
    (forward : Bool) : DrawingPlanarSATClauseMetadata Variable :=
  ⟨carrierClauseAt (routeBend.equalityLink graph) forward,
    .bend routeBend (if forward then 0 else 1)⟩

@[simp] theorem drawingPlanarSATBendFormulaAt_eq_pair
    {Variable Vertex : Type} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (routeBend : RouteBend) :
    drawingPlanarSATBendFormulaAt
        (Variable := Variable) graph routeBend =
      [carrierClauseAt (routeBend.equalityLink graph) true,
        carrierClauseAt (routeBend.equalityLink graph) false] := by
  simp [drawingPlanarSATBendFormulaAt]

@[simp] theorem drawingPlanarSATBendClauseMetadataFor_eq_pair
    {Variable Vertex : Type} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (routeBend : RouteBend) :
    drawingPlanarSATBendClauseMetadataFor
        (Variable := Variable) graph routeBend =
      [bendClauseMetadataAt graph routeBend true,
        bendClauseMetadataAt graph routeBend false] := by
  simp [drawingPlanarSATBendClauseMetadataFor,
    bendClauseMetadataAt]

/-- The local bend descriptor block is explicitly the forward descriptor
followed by the backward descriptor. -/
theorem bendClauseDescriptors_eq_pair
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routeBend : RouteBend) :
    bendClauseDescriptors source routeBend =
      [metadataClauseDescriptor source
          (bendClauseMetadataAt source.incidenceGraph routeBend true),
        metadataClauseDescriptor source
          (bendClauseMetadataAt source.incidenceGraph routeBend false)] := by
  simp [bendClauseDescriptors]

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
