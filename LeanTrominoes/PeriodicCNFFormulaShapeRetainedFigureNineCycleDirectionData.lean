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

/-- Retained planar source after the clearance scale used before inserting
the fixed Figure 7 neighborhoods. -/
def sourceScaledForFigureSeven
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :=
  (finalCoordinatedSource source).scale
    retainedAngularFanSourceClearanceFactor

/-- Matching scaled placement of the retained source variables. -/
def placementScaledForFigureSeven
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :=
  (finalCoordinatedPlacement source).scale
    retainedAngularFanSourceClearanceFactor

/-- Matching scaled route family used to choose the eight compass ports. -/
def routesScaledForFigureSeven
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  PositionedPeriodicCNF.scaleIncidenceRoutes
    retainedAngularFanSourceClearanceFactor
    (finalCoordinatedSourceRoutes source)

/-- Exact route-induced port assignment used by the final scaled Figure 7
formula. -/
def occurrencePortsForFigureSeven
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : OccurrencePorts :=
  occurrencePortsOfAngularOrder
    (sourceScaledForFigureSeven source).erase
    (angularOccurrenceOrder
      (sourceScaledForFigureSeven source).erase
      (routesScaledForFigureSeven source))

/-- Number of copied clauses preceding the implication-cycle suffix. -/
def copiedClauseCount
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : Nat :=
  (occurrenceClauses
    (sourceScaledForFigureSeven source)
    (occurrencePortsForFigureSeven source)).length

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
