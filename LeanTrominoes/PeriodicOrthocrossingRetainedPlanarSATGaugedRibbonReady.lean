/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedPeriodicContinuousPlanarity
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedRoutePointContacts

/-!
# Ribbon readiness of the final gauged periodic drawing

The continuous-planarity and endpoint-contact certificates for the final
periodic planar-SAT drawing assemble into the source geometry required for
ribbon thickening.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- The final gauged periodic incidence drawing is ready for topological
ribbon thickening. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_isRibbonReady
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ []) :
    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
      formula).IsRibbonReady :=
  ⟨retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_isContinuouslyPlanar
      formula wellFormed degree isLocal clausesNonempty,
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_routePointsMeetOnlyAtEndpoints
      formula wellFormed degree isLocal clausesNonempty⟩

end PeriodicOrthocrossing
end LeanTrominoes
