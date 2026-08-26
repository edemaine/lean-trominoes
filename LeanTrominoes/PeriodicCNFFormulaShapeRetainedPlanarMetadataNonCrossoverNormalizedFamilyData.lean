/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverNormalizedPrefixData

/-! # Four non-crossover normalized metadata families -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

def carrierMetadataNormalizedClauses
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List (PeriodicClause (WrappedPeriodicPlanarSATVariable Variable)) :=
  (retainedDrawingPlanarSATCarrierClauseMetadata
    source.incidenceGraph).map (normalizedClause source)

def bendMetadataNormalizedClauses
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List (PeriodicClause (WrappedPeriodicPlanarSATVariable Variable)) :=
  (drawingPlanarSATBendClauseMetadata
    source.incidenceGraph).map (normalizedClause source)

def routedClauseMetadataNormalizedClauses
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List (PeriodicClause (WrappedPeriodicPlanarSATVariable Variable)) :=
  (drawingPlanarSATRoutedClauseMetadata source).map
    (normalizedClause source)

def routedVariableMetadataNormalizedClauses
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List (PeriodicClause (WrappedPeriodicPlanarSATVariable Variable)) :=
  (drawingPlanarSATRoutedVariableClauseMetadata source).map
    (normalizedClause source)

/-- The established four-family suffix unfolds into its named family blocks
without changing presentation order. -/
theorem nonCrossoverMetadataNormalizedClauses_eq_families
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    nonCrossoverMetadataNormalizedClauses source =
      carrierMetadataNormalizedClauses source ++
        bendMetadataNormalizedClauses source ++
          routedClauseMetadataNormalizedClauses source ++
            routedVariableMetadataNormalizedClauses source := by
  simp [nonCrossoverMetadataNormalizedClauses,
    carrierMetadataNormalizedClauses,
    bendMetadataNormalizedClauses,
    routedClauseMetadataNormalizedClauses,
    routedVariableMetadataNormalizedClauses,
    List.map_append]

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
