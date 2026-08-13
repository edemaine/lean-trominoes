/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedEightOccurrenceSplit
import LeanTrominoes.PeriodicEightOccurrenceSplitCanonicalAngularRoutes

/-!
# Routes for the retained fixed-eight occurrence split

The generic angular-splice construction supplies the translated Figure 7
cycle routes and fan spokes for every positioned source.  This module
instantiates that construction at the final retained planar-SAT formula.

The copied source incidences use canonical orthogonal prefixes from their
clause vertices to the appropriate angular fan boundaries.  Consequently the
resulting complete drawing already has exact periodic incidence endpoints and
is orthogonal.  The prefixes deliberately carry no noncrossing claim; replacing
them by prefixes inherited from the retained planar drawing is the remaining
global planarity obligation.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

set_option maxHeartbeats 800000

/-- Complete angular-spliced route family for the retained fixed-eight
occurrence split. -/
def retainedDrawingEightOccurrenceSplitAngularSplicedIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  PeriodicEightOccurrenceSplitPositioned.canonicalAngularSplicedIncidenceRoutes
    (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      source)
    (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source)
    (retainedDrawingAngularOccurrenceOrder source)

/-- The retained angular-spliced drawing realizes exactly the incidence graph
of the retained fixed-eight formula. -/
theorem
    retainedDrawingEightOccurrenceSplitAngularSplicedIncidenceDrawing_routesMatch
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (PositionedPeriodicCNF.incidenceDrawing
      (retainedDrawingEightOccurrenceSplitPositionedFormula source)
      (retainedDrawingEightOccurrenceSplitPlacement source)
      (retainedDrawingEightOccurrenceSplitAngularSplicedIncidenceRoutes
        source)).RoutesMatch
      (retainedDrawingEightOccurrenceSplitPositionedFormula
        source).erase.incidenceGraph := by
  exact
    PeriodicEightOccurrenceSplitPositioned.canonicalAngularSplicedIncidenceDrawing_routesMatch
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        source)
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source)
      (retainedDrawingAngularOccurrenceOrder source)
      (by
        simpa [retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement,
          wrappedDrawingPeriodicPlanarSATPlacement] using
          drawingPeriodicPlanarSATPlacement_period_pos source)

/-- Every route in the retained angular-spliced drawing is orthogonal. -/
theorem
    retainedDrawingEightOccurrenceSplitAngularSplicedIncidenceDrawing_isOrthogonal
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (PositionedPeriodicCNF.incidenceDrawing
      (retainedDrawingEightOccurrenceSplitPositionedFormula source)
      (retainedDrawingEightOccurrenceSplitPlacement source)
      (retainedDrawingEightOccurrenceSplitAngularSplicedIncidenceRoutes
        source)).IsOrthogonal := by
  exact
    PeriodicEightOccurrenceSplitPositioned.canonicalAngularSplicedIncidenceDrawing_isOrthogonal
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        source)
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source)
      (retainedDrawingAngularOccurrenceOrder source)

end PeriodicOrthocrossing
end LeanTrominoes
