import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedDrawingCompatibility
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedRoutePointContacts
import LeanTrominoes.RetainedFinalSourceIncidenceDistinctness
import LeanTrominoes.RetainedAngularTerminalDataProfile

/-!
# Distinct terminal gates in the final retained drawing

This module instantiates the source-level terminal-vector theorem at the
complete retained planar-SAT drawing.  Its compatibility, endpoint-contact,
and incidence-key certificates force genuine occurrences of each variable
to have different backwards terminal vectors.  The generic angular-profile
theorem then turns this fact into duplicate-free radial splice gates.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit

set_option maxHeartbeats 2000000

/-- Genuine occurrences of a variable in the final retained source have
different backwards terminal vectors. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_terminalVectorsInjective
    {Variable : Type*}
    [variableDecidableEq : DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ []) :
    RetainedOccurrenceTerminalVectorsInjective
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).erase
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        formula) := by
  apply
    @retainedOccurrenceTerminalVectorsInjective_of_drawing_eq
      (WrappedPeriodicPlanarSATVariable Variable)
      (fun first second =>
        @instDecidableEqWrappedPeriodicVariable
          (PeriodicPlanarSATVariable Variable)
          (fun firstOriginal secondOriginal =>
            @instDecidableEqPeriodicPlanarSATVariable
              Variable variableDecidableEq
              firstOriginal secondOriginal)
          first second)
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula)
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        formula)
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
        formula)
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_eq
        formula)
  · exact
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_isCompatible
        formula wellFormed degree isLocal clausesNonempty
  · exact
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_routePointsMeetOnlyAtEndpoints
        formula wellFormed degree isLocal clausesNonempty
  · exact
      retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_allIncidenceKeysNodup
        formula wellFormed degree isLocal

/-- Every length-aware angular profile extracted from the final retained
drawing has duplicate-free radial splice gates. -/
theorem retainedDrawingAngularTerminalProfile_gatesDistinct
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    (fits :
      FitsEightSlots
        (retainedDrawingAngularOccurrenceOrder formula))
    (atom : WrappedPeriodicPlanarSATVariable Variable) :
    (retainedDrawingAngularTerminalProfile
      formula wellFormed degree isLocal clausesNonempty
      fits atom).GatesDistinct := by
  have vectorsInjective :=
    retainedDeduplicatedGaugedWrappedDrawing_terminalVectorsInjective
      formula wellFormed degree isLocal clausesNonempty
  unfold retainedDrawingAngularTerminalProfile
  apply
    PeriodicEightOccurrenceSplit.retainedAngularTerminalProfile_gatesDistinct
  exact vectorsInjective

end PeriodicOrthocrossing
end LeanTrominoes
