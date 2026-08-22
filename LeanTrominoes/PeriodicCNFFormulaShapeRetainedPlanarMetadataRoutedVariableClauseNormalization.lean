/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableClauseData
import LeanTrominoes.PeriodicEqualityNormalization

/-! # Normalized retained routed-variable clauses -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Periodicize an external routed node, wrap its prototype, and incorporate
the canonical variable gauge. -/
def externalWrappedVariableNormalization
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (node : PlanarSATNode Variable) :
    WrappedPeriodicPlanarSATVariable Variable × Cell :=
  let normalized :=
    normalizePlanarSATVariable source
      (planarSATExternalVariableMap node)
  let wrapped : WrappedPeriodicPlanarSATVariable Variable :=
    ⟨normalized.1⟩
  (wrapped,
    Cell.add normalized.2
      (retainedDrawingWrappedPeriodicPlanarSATVariableGauge
        source wrapped))

/-- Mapping one active routed-variable equality through the complete
retained periodic normalization pipeline gives the generic pair of
normalized implication clauses. -/
theorem routedVariableLink_normalizedClauses_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (site : VariableRouteSite Variable)
    (armIndex : Nat)
    (arm : DuplicatorArm)
    (link : EqualityLink (PlanarSATNode Variable)) :
    (drawingPlanarSATRoutedVariableClauseMetadataFor
        site armIndex arm link).map
        (normalizedClause source) =
      (([PeriodicEquality.normalizeLink
          (externalWrappedVariableNormalization source) link].product
        [true, false]).map PeriodicEquality.normalizedClause) := by
  rw [← PeriodicEquality.equalityInstance_normalized
    (externalWrappedVariableNormalization source) link]
  simp [drawingPlanarSATRoutedVariableClauseMetadataFor,
    drawingPlanarSATRoutedVariableFormulaAt, equalityInstance,
    normalizedClause, externalWrappedVariableNormalization,
    periodicizePlanarSATClause, periodicizePlanarSATLiteral,
    planarSATExternalVariableMap,
    EmbeddedClause.rename, EmbeddedClause.map,
    wrapPeriodicPlanarSATClause, wrapPeriodicPlanarSATLiteral,
    PeriodicEquality.periodicizeClause,
    PeriodicEquality.periodicizeLiteral,
    PeriodicClause.variableGauge,
    PeriodicLiteral.variableGauge]

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
