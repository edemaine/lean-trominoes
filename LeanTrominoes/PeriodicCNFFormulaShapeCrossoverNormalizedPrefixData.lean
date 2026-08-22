/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCrossoverNormalizedFamily

/-! # Non-crossover suffix of normalized retained clauses -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- The normalized carrier, bend, routed-clause, and routed-variable families,
in their retained presentation order. -/
def nonCrossoverMetadataNormalizedClauses
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List (PeriodicClause (WrappedPeriodicPlanarSATVariable Variable)) :=
  (retainedDrawingPlanarSATCarrierClauseMetadata
      source.incidenceGraph ++
    drawingPlanarSATBendClauseMetadata source.incidenceGraph ++
      drawingPlanarSATRoutedClauseMetadata source ++
        drawingPlanarSATRoutedVariableClauseMetadata source).map
    (normalizedClause source)

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
