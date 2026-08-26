/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineCopiedDirectionData
import LeanTrominoes.PeriodicCNFFormulaShapeFixedEightDirectionData
import LeanTrominoes.PeriodicEightOccurrenceSplitCycleBlockIndex

/-! # Route-based implication-cycle descriptors at retained Figure 9 -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedFigureNineDirection

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicOrthocrossing
open PeriodicThreeSATThree

/-- Exact final positioned implication-cycle suffix, including the outer
Figure 7 routing refinement. -/
def finalCycleClauses
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :=
  (allCycleClauses
      (sourceScaledForFigureSeven source)
      (placementScaledForFigureSeven source)).map
    (PositionedPeriodicClause.scale
      retainedTerminalFanRoutingRefinement)

/-- Route-based descriptor suffix of all positioned implication-cycle
clauses, using their actual global final-route indices. -/
def routedCycleClauseDescriptors
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List FormulaShapeDirectionOrdering.Token :=
  (finalCycleClauses source).zipIdx.map fun taggedClause =>
    .clause
      (FormulaShapeDirectionOrdering.DirectedClauseProfile.ofClause
        (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
          source)
        (copiedClauseCount source + taggedClause.2)
        taggedClause.1)

/-- Final global route lookup viewed in the local clause coordinates of one
source atom's Figure 7 implication ring. -/
def routedCycleRoutesFor
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : WrappedPeriodicPlanarSATVariable Variable) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  fun localClauseIndex literalIndex =>
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
      source
      (copiedClauseCount source +
        (cycleBlockStart
          (sourceVariables
            (sourceScaledForFigureSeven source).erase)
          atom + localClauseIndex))
      literalIndex

/-- Final global route lookup viewed in the local clause coordinates of the
Figure 7 implication ring at a stable source-variable index. -/
def routedCycleRoutesAt
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atomIndex : Nat) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  fun localClauseIndex literalIndex =>
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
      source
      (copiedClauseCount source +
        (FormulaShapeFixedEight.copiesPerVariable * atomIndex +
          localClauseIndex))
      literalIndex

/-- Route-based descriptor block of one source atom's implication ring,
presented against the common local Figure 7 clauses. -/
def routedCycleClauseDescriptorsFor
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : WrappedPeriodicPlanarSATVariable Variable) :
    List FormulaShapeDirectionOrdering.Token :=
  FormulaShapeFixedEightDirection.localCycleFormula.clauses.zipIdx.map
    fun taggedClause =>
      .clause
        (FormulaShapeDirectionOrdering.DirectedClauseProfile.ofClause
          (routedCycleRoutesFor source atom)
          taggedClause.2 taggedClause.1)

/-- Route-based descriptor block of the implication ring at a stable
source-variable index, presented against the common local Figure 7 clauses. -/
def routedCycleClauseDescriptorsAt
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atomIndex : Nat) :
    List FormulaShapeDirectionOrdering.Token :=
  FormulaShapeFixedEightDirection.localCycleFormula.clauses.zipIdx.map
    fun taggedClause =>
      .clause
        (FormulaShapeDirectionOrdering.DirectedClauseProfile.ofClause
          (routedCycleRoutesAt source atomIndex)
          taggedClause.2 taggedClause.1)

/-- Finite local Figure 7 descriptor block repeated once per retained source
variable, in the same phase-major order as the positioned cycle suffix. -/
def finiteCycleClauseDescriptors
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List FormulaShapeDirectionOrdering.Token :=
  (sourceVariables
      (sourceScaledForFigureSeven source).erase).flatMap fun _ =>
    FormulaShapeFixedEightDirection.cycleClauseDescriptors

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

/-- Fully finite phase-major descriptor stream: finite copied-clause lookups,
one fixed local Figure 7 block per retained variable, and the exact output
variable markers. -/
def finiteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List FormulaShapeDirectionOrdering.Token :=
  copiedClauseDescriptors source ++
    finiteCycleClauseDescriptors source ++
      List.replicate
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
          source).erase.variableOccurrences.dedup.length
        .variable

end FormulaShapeRetainedFigureNineDirection
end PeriodicCNF
end LeanTrominoes
