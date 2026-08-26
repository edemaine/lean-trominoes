/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeDirectionOrderingFormulaData
import LeanTrominoes.RetainedAngularFanFinalCoordinatedNormalizedFirstDirections

/-! # Finite copied-clause directions at the retained Figure 9 boundary -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedFigureNineDirection

open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

/-- Finite final direction of one copied retained source incidence.  Direct
incidences use the normalized atlas table; fallbacks retain the scaled source
route direction. -/
def copiedFirstDirection
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat)
    (literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)) :
    AxisDirection :=
  retainedFinalCopiedSourceFirstDirection
    source clauseIndex literalIndex literal

/-- Finite final descriptor of one copied retained source clause. -/
def copiedClauseProfile
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex : Nat)
    (clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)) :
    FormulaShapeDirectionOrdering.DirectedClauseProfile :=
  FormulaShapeDirectionOrdering.DirectedClauseProfile.ofList
    (clause.literals.zipIdx.map fun taggedLiteral =>
      (FormulaShapeDirectionOrdering.literalProfile taggedLiteral.1,
        copiedFirstDirection source clauseIndex taggedLiteral.2
          taggedLiteral.1))

/-- Phase-major descriptor prefix of all copied retained source clauses. -/
def copiedClauseDescriptors
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List FormulaShapeDirectionOrdering.Token :=
  (finalCoordinatedSource source).clauses.zipIdx.map fun taggedClause =>
    .clause
      (copiedClauseProfile source taggedClause.2 taggedClause.1)

/-- Zero-positioned occurrence-renamed view of one copied source clause.
Displayed coordinates are irrelevant to direction descriptors. -/
def copiedOccurrenceClause
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex : Nat)
    (clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)) :
    PositionedPeriodicClause
      (ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable)) where
  position := (0, 0)
  literals :=
    PeriodicEightOccurrenceSplit.occurrenceClause
      (retainedDrawingAngularOccurrencePorts source)
      clauseIndex clause.literals

/-- Semantic route-based descriptor of one copied retained clause before the
finite direct/fallback direction lookup is substituted. -/
def routedCopiedClauseProfile
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex : Nat)
    (clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)) :
    FormulaShapeDirectionOrdering.DirectedClauseProfile :=
  FormulaShapeDirectionOrdering.DirectedClauseProfile.ofClause
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
      source)
    clauseIndex
    (copiedOccurrenceClause source clauseIndex clause)

/-- Route-based descriptor prefix of all copied retained clauses. -/
def routedCopiedClauseDescriptors
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List FormulaShapeDirectionOrdering.Token :=
  (finalCoordinatedSource source).clauses.zipIdx.map fun taggedClause =>
    .clause
      (routedCopiedClauseProfile source taggedClause.2 taggedClause.1)

end FormulaShapeRetainedFigureNineDirection
end PeriodicCNF
end LeanTrominoes
