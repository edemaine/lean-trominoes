/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingBendPerturbation
import LeanTrominoes.Common.Geometry.GridSegmentPerturbationTranslation
import LeanTrominoes.SAT.Planar.EmbeddedCNFIncidenceDrawingMapPoints

/-! # Exact lifted vertex coordinates and perturbation bounds for moved segments -/
namespace LeanTrominoes.PeriodicGridDrawing.InteriorBends

theorem lifted_point_at_vertex {grid factor : Int} {vertex base : Cell}
    (bounds : 0<vertex.1 ∧ vertex.1<grid ∧ 0<vertex.2 ∧ vertex.2<grid)
    (routeCell vertexCell : Cell)
    (equal : Cell.add base (Cell.scale grid routeCell)=Cell.add vertex (Cell.scale grid vertexCell)) :
    Cell.add (point grid factor base) (Cell.scale (factor*grid) routeCell)=
      Cell.add (Cell.scale factor vertex) (Cell.scale (factor*grid) vertexCell) := by
  have baseEq : base=Cell.add vertex (Cell.scale grid (Cell.sub vertexCell routeCell)) := by
    have x := congrArg Prod.fst equal
    have y := congrArg Prod.snd equal
    apply Prod.ext <;> simp only [Cell.add,Cell.sub,Cell.scale] at x y ⊢ <;> nlinarith
  rw [baseEq,point_translated_interior bounds]
  apply Prod.ext <;> simp only [Cell.add,Cell.sub,Cell.scale] <;> ring

theorem lifted_point_perturbation (grid factor : Int) (base translate : Cell) :
    GridSegment.PointPerturbation factor (Cell.add (Cell.scale grid translate) base)
      (Cell.add (Cell.scale (factor*grid) translate) (point grid factor base)) := by
  have scaled : Cell.scale factor (Cell.scale grid translate)=Cell.scale (factor*grid) translate := by
    apply Prod.ext <;> simp only [Cell.scale] <;> ring
  simpa only [scaled] using (point_perturbation grid factor base).translate (Cell.scale grid translate)

theorem lifted_segment_perturbation (grid factor : Int) (segment : GridSegment) (translate : Cell) :
    GridSegment.EndpointPerturbation factor (segment.translate (Cell.scale grid translate))
      ((segment.mapPoints (point grid factor)).translate (Cell.scale (factor*grid) translate)) :=
  ⟨lifted_point_perturbation grid factor segment.start translate,
    lifted_point_perturbation grid factor segment.finish translate⟩

end LeanTrominoes.PeriodicGridDrawing.InteriorBends
