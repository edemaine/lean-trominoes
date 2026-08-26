/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineCopiedDirectionData

/-! # Route-based implication-cycle descriptors at retained Figure 9 -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedFigureNineDirection

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicOrthocrossing
open PeriodicThreeSATThree

/-- Route-based descriptor suffix of all positioned implication-cycle
clauses, using their actual global final-route indices. -/
def routedCycleClauseDescriptors
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List FormulaShapeDirectionOrdering.Token :=
  (allCycleClauses
      (sourceScaledForFigureSeven source)
      (placementScaledForFigureSeven source)).zipIdx.map fun taggedClause =>
    .clause
      (FormulaShapeDirectionOrdering.DirectedClauseProfile.ofClause
        (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
          source)
        (copiedClauseCount source + taggedClause.2)
        taggedClause.1)

/-- Route-based, phase-major descriptor stream: copied source clauses,
implication-cycle clauses, then the actual distinct-variable markers. -/
def routedDescriptors
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List FormulaShapeDirectionOrdering.Token :=
  routedCopiedClauseDescriptors source ++
    routedCycleClauseDescriptors source ++
      List.replicate
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
          source).erase.variableOccurrences.dedup.length
        .variable

end FormulaShapeRetainedFigureNineDirection
end PeriodicCNF
end LeanTrominoes
