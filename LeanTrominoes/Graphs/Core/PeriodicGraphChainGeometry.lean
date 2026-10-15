/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Core.PeriodicGraphBendSubdivision
import LeanTrominoes.SAT.Planar.EmbeddedCNFIncidenceDrawingMapPoints

/-! # Absolute segment geometry of periodic edge chains -/
namespace LeanTrominoes.PeriodicGraph.BendSubdivision

def absoluteSegment {V : Type*} (position : V → Cell) (period : Int) (sourceCell : V → Cell)
    (edge : PeriodicEdge V) : GridSegment :=
  ⟨Cell.add (position edge.source) (Cell.scale period (sourceCell edge.source)),
    Cell.add (position edge.target) (Cell.scale period (Cell.add (sourceCell edge.source) edge.offset))⟩

theorem chainEdges_absoluteSegments {V : Type*} (position : V → Cell) (period : Int) (sourceCell : V → Cell)
    {points : List (V × Cell)} (labels : ∀ entry∈points.dropLast, sourceCell entry.1=entry.2) :
    gridPolylineSegments (points.map (fun entry => Cell.add (position entry.1) (Cell.scale period entry.2)))=
      (chainEdges points).map (absoluteSegment position period sourceCell) := by
  induction points using List.twoStepInduction with
  | nil | singleton => rfl
  | cons_cons first second rest _ induction =>
      have firstLabel := labels first (by simp only [List.dropLast_cons_cons,List.mem_cons,true_or])
      have tailLabels : ∀ entry∈(second::rest).dropLast, sourceCell entry.1=entry.2 := by
        intro entry member
        apply labels entry
        rw [List.dropLast_cons_cons]
        exact List.mem_cons_of_mem first member
      simp only [List.map_cons,gridPolylineSegments,chainEdges]
      congr 1
      · unfold absoluteSegment
        congr 1
        · simp only [firstLabel]
        · apply Prod.ext <;> simp only [firstLabel,Cell.add,Cell.scale,Cell.sub] <;> ring
      · exact induction second tailLabels

end LeanTrominoes.PeriodicGraph.BendSubdivision
