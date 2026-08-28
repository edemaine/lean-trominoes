/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierNormalizationInjectivity
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeNormalizedSourceKeySemantics
import LeanTrominoes.PeriodicOrthocrossingRetainedCompactAtomWord

/-! # Compact carrier words and wrapped semantic normalization -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- A graph-period compact carrier-node word is the final compact word of
the same endpoint after wrapped semantic normalization. -/
theorem compactWordAtPeriod_eq_wrappedNormalization
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceWord : Variable → List Bool)
    (node : CarrierNode) :
    CarrierNodeNormalizedSourceKeys.compactWordAtPeriod
        (drawingGridSize source.incidenceGraph) node =
      RetainedCompactAtomWords.word sourceWord
        (carrierWrappedVariableNormalization source node).1 := by
  rw [CarrierNodeNormalizedSourceKeys.compactWordAtPeriod_drawingGridSize
    source.incidenceGraph sourceWord node]
  apply congrArg (RetainedCompactAtomWords.word sourceWord)
  cases node <;> rfl

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
