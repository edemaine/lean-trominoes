/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedPolarityRouteDirectionBlock
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedFormulaComputability
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedPlacementData
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRoutesData
import LeanTrominoes.PeriodicCNFStripSourceFormula

/-! # Compact routed-polarity blocks for the concrete strip source -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget PeriodicOrthocrossing

local instance horizontalRoutedRouteDirectionBlockSourceVariableDecidableEq :
    DecidableEq Variable :=
  Classical.decEq _

/-- The compact retained Figure 9 route vocabulary with one of the four
polarity-normalization stream operations. -/
abbrev HorizontalRoutedRouteDirectionBlock :=
  RetainedPolarityRouteDirectionBlock

/-- Every genuine proof-free routed occurrence of the concrete strip source
has one compact retained-polarity direction block. -/
theorem horizontalRoutedRoute_directionBlock_of_members
    (source : PeriodicCNF Nat)
    {outputClause : PositionedPeriodicClause RoutedVariable}
    {outputClauseIndex : Nat}
    (outputClauseMember :
      (outputClause, outputClauseIndex) ∈
        (horizontalRoutedFormulaComputed source).clauses.zipIdx)
    {outputLiteral : PeriodicLiteral RoutedVariable}
    {outputLiteralIndex : Nat}
    (outputLiteralMember :
      (outputLiteral, outputLiteralIndex) ∈
        outputClause.literals.zipIdx) :
    ∃ block : HorizontalRoutedRouteDirectionBlock,
      unitSubdivisionDirections
          (horizontalRoutedRoutesComputed
            source outputClauseIndex outputLiteralIndex) =
        block.directions RetainedFigureNineRouteDirectionBlock.directions := by
  exact
    retainedOrderedFixedEightPolarityNormalizedRoute_directionBlock_of_members
      (sourceFormula source)
      (sourceFormula_isLocal source)
      (sourceFormula_widthAtMostThree source)
      (sourceFormula_occurrencesAtMostThree_canonicalBEq source)
      (sourceFormula_clausesNonempty source)
      outputClauseMember outputLiteralMember

end PeriodicCNFStripReduction
end LeanTrominoes
