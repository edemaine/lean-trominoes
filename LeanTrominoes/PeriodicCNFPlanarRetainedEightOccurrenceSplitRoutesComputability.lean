import LeanTrominoes.PeriodicCNFPlanarRetainedEightOccurrenceSplitRoutes
import LeanTrominoes.PeriodicCNFPlanarRetainedEightOccurrenceSplitPositionedComputability
import LeanTrominoes.PeriodicEightOccurrenceSplitPositionedRouteLookupComputability

/-!
# Computability of retained fixed-eight routes

The terminal-angle order of retained planar-SAT incidences is computable from
the exact retained route lookup.  Specializing the generic positioned route
compiler therefore computes the existing canonical angular-spliced Figure 7
route family, including copied incidences and the appended implication rings.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 1800000

theorem retainedDrawingAngularOccurrenceOrder_copies_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : PeriodicCNF Variable ×
        WrappedPeriodicPlanarSATVariable Variable =>
      (retainedDrawingAngularOccurrenceOrder input.1).copies input.2 := by
  change Primrec fun input : PeriodicCNF Variable ×
      WrappedPeriodicPlanarSATVariable Variable =>
    PeriodicThreeSATThree.angularOccurrenceVariables
      (retainedPlanarSATFormula input.1)
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        input.1) input.2
  exact PeriodicThreeSATThree.angularOccurrenceVariables_primrec
    retainedPlanarSATFormula
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
    retainedPlanarSATFormula_primrec
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_primrec

theorem retainedDrawingEightOccurrenceSplitAngularSplicedIncidenceRoutes_eq_data
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    retainedDrawingEightOccurrenceSplitAngularSplicedIncidenceRoutes source =
      PeriodicEightOccurrenceSplitPositioned.canonicalAngularSplicedIncidenceRoutesData
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          source)
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source)
        (retainedDrawingAngularOccurrencePorts source)
        (retainedDrawingAngularOccurrenceOrder source).copies := by
  unfold retainedDrawingEightOccurrenceSplitAngularSplicedIncidenceRoutes
  exact
    PeriodicEightOccurrenceSplitPositioned.canonicalAngularSplicedIncidenceRoutes_eq_data
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        source)
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source)
      (retainedDrawingAngularOccurrenceOrder source)

theorem
    retainedDrawingEightOccurrenceSplitAngularSplicedIncidenceRoutes_computable
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Computable fun input : (PeriodicCNF Variable × Nat) × Nat =>
      retainedDrawingEightOccurrenceSplitAngularSplicedIncidenceRoutes
        input.1.1 input.1.2 input.2 := by
  exact
    (PeriodicEightOccurrenceSplitPositioned.canonicalAngularSplicedIncidenceRoutesData_computable
      (Input := PeriodicCNF Variable)
      (Variable := WrappedPeriodicPlanarSATVariable Variable)
      retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
      retainedDrawingAngularOccurrencePorts
      (fun input => (retainedDrawingAngularOccurrenceOrder input).copies)
      retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_primrec
      retainedGaugedWrappedDrawingPeriodicPlanarSATPeriod_primrec
      retainedGaugedWrappedDrawingPeriodicPlanarSATPosition_primrec
      retainedDrawingAngularOccurrencePorts_port_primrec
      retainedDrawingAngularOccurrenceOrder_copies_primrec).of_eq
        fun input => congrFun
          (congrFun
            (retainedDrawingEightOccurrenceSplitAngularSplicedIncidenceRoutes_eq_data
              input.1.1).symm
            input.1.2)
          input.2

end PeriodicOrthocrossing
end LeanTrominoes
