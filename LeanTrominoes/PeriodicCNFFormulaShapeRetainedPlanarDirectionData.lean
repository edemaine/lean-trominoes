/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeDirectionOrderingFormulaData
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATVariableGauge

/-! # Direction descriptors of the retained planar source -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarDirection

open PeriodicOrthocrossing

/-- The positioned retained planar-SAT presentation before fixed-eight
occurrence splitting. -/
abbrev positionedSource {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :=
  retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
    source

/-- Its exact retained incidence-route family. -/
abbrev incidenceRoutes {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :=
  retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
    source

/-- One finite literal-profile/first-direction descriptor per retained
planar clause, followed by the distinct-variable markers. -/
def descriptors {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List FormulaShapeDirectionOrdering.Token :=
  FormulaShapeDirectionOrdering.ofFormula
    (positionedSource source) (incidenceRoutes source)

/-- The retained planar formula after stable clockwise sorting by its actual
clause-side route exits. -/
def orderedSource {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :=
  PositionedPeriodicCNF.orderClausesByRouteDirection
    (positionedSource source) (incidenceRoutes source)

/-- Ordinary finite formula shape obtained from the retained direction
descriptors. -/
def shape {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : List FormulaShape.Token :=
  FormulaShapeDirectionOrdering.shape (descriptors source)

end FormulaShapeRetainedPlanarDirection
end PeriodicCNF
end LeanTrominoes
