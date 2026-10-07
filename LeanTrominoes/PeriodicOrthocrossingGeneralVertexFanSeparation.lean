/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicOrthocrossingGeneralVertexBounds
import LeanTrominoes.PeriodicOrthocrossingGeneralRouteFans

/-! # A vertex center in a fan is that fan's own vertex endpoint -/
namespace LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
attribute [local irreducible] fan

theorem indexed_vertex_fan_contact {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) (orthogonal : Bool) {index : Nat} (valid : index < graph.vertices.length)
    {port : GraphPort Vertex} (member : port ∈ allPorts graph) {vertexCell fanCell : Cell}
    (contains : GridPolyline.RealContains
      (translatePolyline (Cell.scale (drawingGridSize graph : Int) fanCell) (fan graph orthogonal port))
      (realCell (Cell.add (Cell.scale (drawingGridSize graph : Int) vertexCell) (position graph index)))) :
    vertexCell = fanCell ∧ position graph index = (vertexX graph port.vertex,2) := by
  let point := realCell (Cell.add (Cell.scale (drawingGridSize graph : Int) vertexCell) (position graph index))
  change GridPolyline.RealContains (translatePolyline (Cell.scale (drawingGridSize graph : Int) fanCell)
    (fan graph orthogonal port)) point at contains
  have image := (GridPolyline.realContains_translate_inverse _ _ _).mp contains
  have box := fan_real_block_bounds orthogonal member image
  simp only [Cell.scale,Prod.fst,Prod.snd,Int.cast_mul,Int.cast_natCast] at box
  have vertexBounds := indexed_vertex_bounds wellFormed valid
  have fanBlock := fan_block_bounds wellFormed member
  have gridPositive : (0 : Int) < drawingGridSize graph := by exact_mod_cast drawingGridSize_pos graph
  have gridThree : (3 : Int) < drawingGridSize graph := by unfold drawingGridSize; omega
  have px : point.1 = ((position graph index).1 : ℝ)+(drawingGridSize graph : ℝ)*vertexCell.1 := by
    simp [point,realCell,Cell.add,Cell.scale,add_comm]
  have py : point.2 = ((2 : Int) : ℝ)+(drawingGridSize graph : ℝ)*vertexCell.2 := by
    simp [point,realCell,position,Cell.add,Cell.scale,add_comm]
  have vertexXBand : ((position graph index).1 : ℝ)+(drawingGridSize graph : ℝ)*vertexCell.1 ≤ point.1 ∧
      point.1 ≤ ((position graph index).1 : ℝ)+(drawingGridSize graph : ℝ)*vertexCell.1 := ⟨px.ge,px.le⟩
  have vertexYBand : ((2 : Int) : ℝ)+(drawingGridSize graph : ℝ)*vertexCell.2 ≤ point.2 ∧
      point.2 ≤ ((2 : Int) : ℝ)+(drawingGridSize graph : ℝ)*vertexCell.2 := ⟨py.ge,py.le⟩
  have fanXBand : (fanBlockStart graph port.vertex : ℝ)+(drawingGridSize graph : ℝ)*fanCell.1 ≤ point.1 ∧
      point.1 ≤ (fanBlockFinish graph port.vertex : ℝ)+(drawingGridSize graph : ℝ)*fanCell.1 :=
    ⟨by linarith [box.1],by linarith [box.2.1]⟩
  have fanYBand : ((1 : Int) : ℝ)+(drawingGridSize graph : ℝ)*fanCell.2 ≤ point.2 ∧
      point.2 ≤ ((3 : Int) : ℝ)+(drawingGridSize graph : ℝ)*fanCell.2 := by
    norm_num only [Int.cast_ofNat]
    exact ⟨by linarith [box.2.2.1],by linarith [box.2.2.2]⟩
  have xShifts := GridSegment.normalized_bands_periodic_shifts_unique (point := point.1) gridPositive
    (by omega : 0 ≤ (position graph index).1 ∧ (position graph index).1 < drawingGridSize graph)
    (by omega : 0 ≤ fanBlockStart graph port.vertex ∧ fanBlockFinish graph port.vertex < drawingGridSize graph)
    vertexXBand fanXBand
  have yShifts := GridSegment.normalized_bands_periodic_shifts_unique (point := point.2) gridPositive
    (by omega : (0 : Int) ≤ 2 ∧ (2 : Int) < drawingGridSize graph)
    (by omega : (0 : Int) ≤ 1 ∧ (3 : Int) < drawingGridSize graph) vertexYBand fanYBand
  have cells : vertexCell = fanCell := Prod.ext xShifts yShifts
  have lower : fanBlockStart graph port.vertex ≤ (position graph index).1 := by
    rw [← xShifts] at fanXBand
    exact_mod_cast (by linarith [px,fanXBand.1] : (fanBlockStart graph port.vertex : ℝ) ≤ (position graph index).1)
  have upper : (position graph index).1 ≤ fanBlockFinish graph port.vertex := by
    rw [← xShifts] at fanXBand
    exact_mod_cast (by linarith [px,fanXBand.2] : ((position graph index).1 : ℝ) ≤ fanBlockFinish graph port.vertex)
  have vertexIndexValid : index < (degrees graph).length := by simpa [degrees] using valid
  have indices : index = graph.vertices.idxOf port.vertex := by
    rcases lt_trichotomy index (graph.vertices.idxOf port.vertex) with less | equal | greater
    · have separated := block_separated (degrees graph) vertexIndexValid less
      simp only [fanBlockStart,position] at lower
      omega
    · exact equal
    · have separated := fan_block_finish_before_index wellFormed member greater
      simp only [position] at upper
      omega
  refine ⟨cells,?_⟩
  simp only [position,vertexX,indices]

end LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
