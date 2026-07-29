import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedDrawingCompatibility
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATRasterizedDrawing
import LeanTrominoes.PositionedPeriodicCNFCanonicalOrthogonalPlanarization
import LeanTrominoes.PositionedPeriodicCNFScaling

/-!
# Planarized retained planar-SAT incidence presentation

The retained planar-SAT construction has a compatible oblique reference
drawing.  Positive scaling preserves its route-independent vertex geometry.
The retained-ray rasterization supplies exact orthogonal replacement routes
over those scaled vertices, and ordered unit subdivision then proves the
project's integer-grid planarity predicate.

The resulting `PlanarIncidencePresentation` is the first complete planar,
orthogonal, graph-compatible presentation of the retained planar-SAT
incidence graph.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Positive scaling preserves compatibility of the original retained
reference drawing with the scaled positioned incidence graph. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATScaledReferenceIncidenceDrawing_isCompatible
    {Variable : Type*} [DecidableEq Variable]
    {factor : Nat} (factorPositive : 0 < factor)
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ []) :
    (PositionedPeriodicCNF.incidenceDrawing
      ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).scale factor)
      ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
        formula).scale factor)
      (PositionedPeriodicCNF.scaleIncidenceRoutes factor
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
          formula))).IsCompatible
      ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).scale factor).erase.incidenceGraph := by
  have periodPositive :
      0 <
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).period := by
    simpa [retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement,
      wrappedDrawingPeriodicPlanarSATPlacement] using
      drawingPeriodicPlanarSATPlacement_period_pos formula
  rw [PositionedPeriodicCNF.incidenceDrawing_scale
    factor
    (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula)
    (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
      formula)
    periodPositive]
  simpa only [PositionedPeriodicCNF.erase_scale,
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing] using
    PeriodicGridDrawing.isCompatible_scale
      factorPositive
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).erase.incidenceGraph
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
        formula)
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_isCompatible
        formula wellFormed degree isLocal clausesNonempty)

/-- Rasterize and unit-subdivide the retained planar-SAT routes to obtain a
complete compatible, orthogonal, planar incidence presentation. -/
def
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATPlanarIncidencePresentation
    {Variable : Type*} [DecidableEq Variable]
    {factor : Nat} (factorPositive : 0 < factor)
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ []) :
    PositionedPeriodicCNF.PlanarIncidencePresentation
      ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).scale factor)
      ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
        formula).scale factor) := by
  have periodPositive :
      0 <
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).period := by
    simpa [retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement,
      wrappedDrawingPeriodicPlanarSATPlacement] using
      drawingPeriodicPlanarSATPlacement_period_pos formula
  exact
    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATRasterizedCanonicalRoutes
      factorPositive formula wellFormed degree isLocal clausesNonempty
    ).unitSubdividedPlanarPresentation
      (Nat.mul_pos factorPositive periodPositive)
      (PositionedPeriodicCNF.scaleIncidenceRoutes factor
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
          formula))
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATScaledReferenceIncidenceDrawing_isCompatible
        factorPositive formula wellFormed degree isLocal clausesNonempty)

end PeriodicOrthocrossing
end LeanTrominoes
