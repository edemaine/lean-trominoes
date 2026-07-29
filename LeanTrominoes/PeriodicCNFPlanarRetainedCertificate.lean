import LeanTrominoes.PeriodicCNFPlanarRetainedFinalCorrectness
import LeanTrominoes.PeriodicCNFPlanarRetainedNonempty
import LeanTrominoes.PeriodicCNFPlanarRetainedWidth
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedDegree
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedDrawingCompatibility
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedRibbonReady
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedRouteBounds
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATPlanarizedDrawing

/-!
# Final certificate for retained periodic planar SAT

This module packages the retained planarization endpoint behind the ordinary
local 3SAT-3 hypotheses used by the hardness reduction.  The output is
equisatisfiable with its source, has width at most three and occurrence degree
at most eight, and carries the complete continuously planar, endpoint-clean,
halo-bounded incidence drawing constructed by the retained geometry modules.

The certificate deliberately does not claim that this pre-split drawing is
orthogonal.  Variables in the Figure 8 gadgets can have degree greater than
four, and their direct incidence routes use the eight axis and diagonal
terminal rays.  The fixed-eight occurrence split is the later stage that
turns those rays into an orthogonal degree-three drawing.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Short opaque name for the final retained periodic CNF. -/
def retainedPlanarSATFormula
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PeriodicCNF (WrappedPeriodicPlanarSATVariable Variable) :=
  (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
    source).erase

/-- The complete logical and geometric contract delivered by retained
planarization before fixed-eight occurrence splitting. -/
structure RetainedPlanarSATCertificate
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : Prop where
  graphWellFormed :
    source.incidenceGraph.IsWellFormed
  graphDegreeAtMostThree :
    source.incidenceGraph.DegreeAtMost 3
  graphIsLocal :
    source.incidenceGraph.IsLocal
  sourceSatisfiableIff :
    (retainedPlanarSATFormula source).Satisfiable ↔
      source.Satisfiable
  widthAtMostThree :
    (retainedPlanarSATFormula source).WidthAtMost 3
  occurrencesAtMostEight :
    (retainedPlanarSATFormula source).OccurrencesAtMost 8
  clausesNonempty :
    ∀ clause ∈ (retainedPlanarSATFormula source).clauses,
      clause ≠ []
  drawingCompatible :
    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
      source).IsCompatible
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          source).erase.incidenceGraph
  drawingRibbonReady :
    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
      source).IsRibbonReady
  routePointsInside :
    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
      source).RoutePointsInExpandedSquare
  planarIncidencePresentation :
    Nonempty
      (PositionedPeriodicCNF.PlanarIncidencePresentation
        ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          source).scale 1)
        ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          source).scale 1))

/-- Every local width-three, three-occurrence CNF with no empty clause has
the complete retained planar-SAT certificate. -/
theorem retainedPlanarSATCertificate
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    RetainedPlanarSATCertificate source := by
  have graphWellFormed :
      source.incidenceGraph.IsWellFormed :=
    PeriodicCNF.incidenceGraph_isWellFormed source
  have graphDegree :
      source.incidenceGraph.DegreeAtMost 3 :=
    PeriodicCNF.incidenceGraph_degreeAtMost
      sourceWidth sourceOccurrences
  have graphLocal :
      source.incidenceGraph.IsLocal :=
    PeriodicCNF.incidenceGraph_isLocal sourceLocal
  have retainedClausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula source,
        clause.literals ≠ [] :=
    retainedDrawingPlanarSATFormula_clausesNonempty_of_source
      source sourceClausesNonempty
  exact {
    graphWellFormed := graphWellFormed
    graphDegreeAtMostThree := graphDegree
    graphIsLocal := graphLocal
    sourceSatisfiableIff := by
      simpa only [retainedPlanarSATFormula] using
        retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATFormula_source_satisfiable_iff
          source graphWellFormed graphDegree graphLocal sourceOccurrences
    widthAtMostThree := by
      simpa only [retainedPlanarSATFormula] using
        retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_widthAtMostThree
          source sourceWidth
    occurrencesAtMostEight := by
      simpa only [retainedPlanarSATFormula] using
        retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_occurrencesAtMostEight
          graphWellFormed graphDegree graphLocal sourceOccurrences
    clausesNonempty := by
      simpa only [retainedPlanarSATFormula] using
        retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATFormula_clausesNonempty_of_source
          source sourceClausesNonempty
    drawingCompatible :=
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_isCompatible
        source graphWellFormed graphDegree graphLocal
          retainedClausesNonempty
    drawingRibbonReady :=
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_isRibbonReady
        source graphWellFormed graphDegree graphLocal
          retainedClausesNonempty
    routePointsInside :=
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_routePointsInExpandedSquare
        source graphWellFormed graphDegree graphLocal
          retainedClausesNonempty
    planarIncidencePresentation :=
      ⟨retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATPlanarIncidencePresentation
        (by omega) source graphWellFormed graphDegree graphLocal
          retainedClausesNonempty⟩
  }

end PeriodicOrthocrossing
end LeanTrominoes
