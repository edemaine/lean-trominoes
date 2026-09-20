/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarThreeOccurrenceGeometry
import LeanTrominoes.PeriodicCNFIncidenceGraphSize

/-! # A linear fundamental-grid bound for the constructed planar 3SAT-3 drawing -/
namespace LeanTrominoes.PeriodicPlanarSAT.ThreeOccurrenceGeometry
open PeriodicOrthocrossing PeriodicEightOccurrenceSplit
variable {V : Type} [DecidableEq V]

/-- Every refinement in the retained drawing has a fixed scale. -/
theorem period_eq (f : PeriodicCNF V) :
    (placement f).period =
      737280 * (f.incidenceGraph.vertices.length+f.incidenceGraph.edges.length+1) := by
  simp only [placement,retainedFigureNineClearancePlacement,PeriodicVariablePlacement.scale_period,
    retainedFigureNineSourceClearanceFactor,retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement,
    retainedAngularFanSourceScaledRefinedPlacement,retainedAngularFanRefinedPlacement,
    PeriodicEightOccurrenceSplitPositioned.placement,retainedTerminalFanRoutingRefinement,
    retainedAngularFanSourceClearanceFactor,PeriodicEightOccurrenceSplitPositioned.refinementScale,
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_period,wrappedDrawingPeriodicPlanarSATPlacement,
    drawingPeriodicPlanarSATPlacement,planarMacroScale,drawingGridSize]
  rw [show (36 : Int).toNat=36 from rfl,show (20 : Int).toNat=20 from rfl]
  ring

/-- The side length is linear in the source's clause-plus-literal count. -/
theorem period_le_presentationSize (f : PeriodicCNF V) :
    (placement f).period ≤ 737280 * (2*f.presentationSize+1) := by
  rw [period_eq]
  have vertices := PeriodicCNF.incidenceGraph_vertices_length_le f
  rw [PeriodicCNF.incidenceGraph_edges_length]
  unfold PeriodicCNF.presentationSize
  omega

theorem drawing_period_le_presentationSize (f : PeriodicCNF V) :
    (drawing f).gridSize ≤ 737280 * (2*f.presentationSize+1) := by
  unfold drawing
  rw [PositionedPeriodicCNF.incidenceDrawing_gridSize _ _ _
    (retainedFigureNineClearancePlacement_period_pos f)]
  exact period_le_presentationSize f

end LeanTrominoes.PeriodicPlanarSAT.ThreeOccurrenceGeometry
