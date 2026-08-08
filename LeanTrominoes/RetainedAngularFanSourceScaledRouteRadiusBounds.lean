import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATRebasedRouteRadiusBounds
import LeanTrominoes.PositionedPeriodicCNFRebasedRouteRadiusScaling
import LeanTrominoes.RetainedAngularFanSourceScaling

/-!
# Variable-centered route bounds after retained-source scaling

The fixed-eight construction first scales the retained planar-SAT source by
the clearance factor and only then inserts the local angular fans.  This file
records the corresponding scaled source certificate: every rebased source
route remains within one scaled placement period of its variable center.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit

/-- The retained deduplicated source routes preserve their variable-centered
one-period bound under the fixed source-clearance scaling. -/
theorem retainedDrawingSourceScaledIncidenceRoutes_withinVariablePeriod
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal) :
    PositionedPeriodicCNF.RebasedIncidenceRoutesWithinVariablePeriod
      ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).scale retainedAngularFanSourceClearanceFactor)
      ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula).scale
        retainedAngularFanSourceClearanceFactor)
      (PositionedPeriodicCNF.scaleIncidenceRoutes
        retainedAngularFanSourceClearanceFactor
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
          formula)) := by
  exact
    (retainedDeduplicatedGaugedWrappedDrawingIncidenceRoutes_withinVariablePeriod
      formula wellFormed degree isLocal).scale
        retainedAngularFanSourceClearanceFactor

/-- Source-clearance scaling multiplies the retained one-cell margin along
with every coordinate, leaving room for the later fixed-eight local fan. -/
theorem retainedDrawingSourceScaledIncidenceRoutes_withinVariablePredPeriod
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal) :
    PositionedPeriodicCNF.RebasedIncidenceRoutesWithinVariableRadius
      (retainedAngularFanSourceClearanceFactor *
        ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula).period - 1))
      ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).scale retainedAngularFanSourceClearanceFactor)
      ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula).scale
        retainedAngularFanSourceClearanceFactor)
      (PositionedPeriodicCNF.scaleIncidenceRoutes
        retainedAngularFanSourceClearanceFactor
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
          formula)) := by
  exact
    (retainedDeduplicatedGaugedWrappedDrawingIncidenceRoutes_withinVariablePredPeriod
      formula wellFormed degree isLocal).scale
        retainedAngularFanSourceClearanceFactor

end PeriodicOrthocrossing
end LeanTrominoes
