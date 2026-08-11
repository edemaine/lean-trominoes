import LeanTrominoes.PeriodicCNFPlanarRetainedLocalIncidenceRouteLookupComputability
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATPeriodicizationComputability
import LeanTrominoes.PositionedPeriodicCNFRouteTransportComputability

/-!
# Computability of gauged retained planar-SAT routes

The executable finite retained routes are transported through the exact
variable-gauge, clause-anchor normalization, and first-orbit deduplication
used by `retainedPlanarSATFormula`.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 3000000

private theorem retainedGaugedWrappedDrawingPeriodicPlanarSATPeriod_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun formula : PeriodicCNF Variable =>
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
        formula).period := by
  change Primrec fun formula : PeriodicCNF Variable =>
    planarMacroScale.toNat *
      drawingGridSize (PeriodicCNF.incidenceGraph formula)
  exact Primrec.nat_mul.comp
    (Primrec.const planarMacroScale.toNat)
    (drawingGridSize_primrec.comp PeriodicCNF.incidenceGraph_primrec)

/-- Retained local routes after the canonical variable gauge and first
clause-anchor normalization. -/
def retainedAnchorNormalizedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  PositionedPeriodicCNF.anchorNormalizedIncidenceRoutes
    (retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula formula)
    (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
    (retainedDrawingPlanarSATLocalIncidenceRoutes formula)

theorem
    retainedAnchorNormalizedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : (PeriodicCNF Variable × Nat) × Nat =>
      retainedAnchorNormalizedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        input.1.1 input.1.2 input.2 := by
  exact (PositionedPeriodicCNF.anchorNormalizedIncidenceRoutes_primrec
    (retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula)
    (fun formula =>
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
        formula).period)
    (fun formula =>
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
        formula).position)
    retainedDrawingPlanarSATLocalIncidenceRoutes
    retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_primrec
    retainedGaugedWrappedDrawingPeriodicPlanarSATPeriod_primrec
    retainedDrawingPlanarSATLocalIncidenceRoutes_primrec).of_eq
      fun _ => rfl

theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : (PeriodicCNF Variable × Nat) × Nat =>
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        input.1.1 input.1.2 input.2 := by
  change Primrec fun input : (PeriodicCNF Variable × Nat) × Nat =>
    PositionedPeriodicCNF.deduplicatedIncidenceRoutes
      (retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        input.1.1)
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement input.1.1)
      (retainedAnchorNormalizedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        input.1.1) input.1.2 input.2
  exact PositionedPeriodicCNF.deduplicatedIncidenceRoutes_primrec
    (Input := PeriodicCNF Variable)
    (Variable := WrappedPeriodicPlanarSATVariable Variable)
    (retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula)
    (fun formula =>
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
        formula).period)
    (fun formula =>
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
        formula).position)
    retainedAnchorNormalizedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
    retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_primrec
    retainedGaugedWrappedDrawingPeriodicPlanarSATPeriod_primrec
    retainedAnchorNormalizedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_primrec

theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_computable
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Computable fun input : (PeriodicCNF Variable × Nat) × Nat =>
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        input.1.1 input.1.2 input.2 :=
  retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_primrec.to_comp

end PeriodicOrthocrossing
end LeanTrominoes
