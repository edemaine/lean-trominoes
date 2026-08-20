/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarDirectionData
import LeanTrominoes.PeriodicCNFPlanarRetainedSATClauseIndex

/-! # Metadata presentation of retained planar direction data -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- The exact periodic literal list attached to one retained finite clause
after wrapping, canonical variable gauging, and clause-anchor normalization. -/
def normalizedClause {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (metadata : DrawingPlanarSATClauseMetadata Variable) :
    PeriodicClause (WrappedPeriodicPlanarSATVariable Variable) :=
  ((wrapPeriodicPlanarSATClause
      (periodicizePlanarSATClause source metadata.clause)).variableGauge
    (retainedDrawingWrappedPeriodicPlanarSATVariableGauge source))
      |>.anchorNormalize

/-- Normalized clauses in the exact five-family retained metadata order. -/
def normalizedClauses {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List (PeriodicClause (WrappedPeriodicPlanarSATVariable Variable)) :=
  (retainedDrawingPlanarSATClauseMetadata source).map
    (normalizedClause source)

/-- Exact clause-orbit representatives retained by the final planar source. -/
def deduplicatedClauses {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List (PeriodicClause (WrappedPeriodicPlanarSATVariable Variable)) :=
  (normalizedClauses source).dedup

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
