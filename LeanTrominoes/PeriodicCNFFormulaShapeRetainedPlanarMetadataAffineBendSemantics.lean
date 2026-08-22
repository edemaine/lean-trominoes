/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendStreamSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBendFamilySemantics
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorBendNodup

/-! # Complete semantics of the affine retained-bend scan -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PlanarThreeSAT RouteDescriptorPairFieldTags
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- On every well-formed forward-local degree-three source, the compact
affine descriptor-pair scan is exactly the retained bend descriptor family. -/
theorem affineBendDescriptorStream_eq_bendMetadataClauseDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal) :
    affineBendDescriptorStream
        (encodeDescriptorPairs
          ((PeriodicCNF.numericRouteDescriptors formula) ×ˢ
            (PeriodicCNF.numericRouteDescriptors formula))) =
      bendMetadataClauseDescriptors formula := by
  rw [affineBendDescriptorStream_numericRouteDescriptors
    formula wellFormed degree isLocal forward]
  rw [← List.flatMap_assoc]
  rw [← PeriodicCNF.incidenceGraph_drawingRouteBends_eq_numeric]
  rw [bendMetadataClauseDescriptors_eq_canonicalBlocks]
  simp

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
