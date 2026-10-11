/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendIncidentCoreData
import LeanTrominoes.PeriodicGridDrawingRawBendDirectionBounds
import LeanTrominoes.PeriodicGridDrawingRawBendRayKeys

/-! # Both endpoints of every raw piece supply certified incidence data -/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement PeriodicOrthocrossing

def incidentPort {V : Type*} (tagged : PeriodicEdge (Vertex V) × Nat) (target : Bool) : GraphPort (Vertex V) :=
  if target then targetPort tagged.1 tagged.2 else sourcePort tagged.1 tagged.2

def incidentRawSegment {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge (Vertex V) × Nat) (target : Bool) : GridSegment :=
  if target then (subdivisionSegment source drawing tagged.1).reverse else subdivisionSegment source drawing tagged.1

def incidentAnchoredSegment {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge (Vertex V) × Nat) (target : Bool) : GridSegment :=
  if target then (anchoredSegment source drawing (Cubic.coreFactor drawing.gridSize) tagged).reverse
  else anchoredSegment source drawing (Cubic.coreFactor drawing.gridSize) tagged

theorem incidentCoreData {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    (graphLocal : source.IsLocal) (drawingLocal : drawing.IsRealLocal source)
    {tagged : PeriodicEdge (Vertex V) × Nat} (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (target : Bool) : IncidentCoreData source drawing (incidentPort tagged target)
      (incidentRawSegment source drawing tagged target) (incidentAnchoredSegment source drawing tagged target) := by
  have bounds := subdivisionSegment_direction_bounds planar.1 graphLocal drawingLocal member
  have genuine := subdivision_segment_nonconstant planar member
  have perturbed := anchoredSegment_perturbed source drawing (Cubic.coreFactor drawing.gridSize) tagged
  cases target
  · refine ⟨sourcePort_mem_allPorts _ member,shifted_source_portRayKey source drawing member,genuine,bounds,perturbed,rfl,?_⟩
    intro vertical
    have sameX : (subdivisionSegment source drawing tagged.1).start.1 = (subdivisionSegment source drawing tagged.1).finish.1 := by
      change (subdivisionSegment source drawing tagged.1).direction.1 = 0 at vertical
      simp only [GridSegment.direction] at vertical
      omega
    have coordinates := vertical_anchoredSegment_x planar degree (Cubic.coreFactor drawing.gridSize) member sameX
    simpa only [incidentAnchoredSegment,Bool.false_eq_true,ite_false,coordinates.1,coordinates.2,sameX]
  · refine ⟨targetPort_mem_allPorts _ member,shifted_target_portRayKey source drawing member,?_,?_,perturbed.reverse,rfl,?_⟩
    · exact fun equal => genuine equal.symm
    · change |(subdivisionSegment source drawing tagged.1).reverse.direction.1| ≤ 2*(drawing.gridSize : Int) ∧
        |(subdivisionSegment source drawing tagged.1).reverse.direction.2| ≤ 2*(drawing.gridSize : Int)
      have x : (subdivisionSegment source drawing tagged.1).reverse.direction.1 = -(subdivisionSegment source drawing tagged.1).direction.1 := by
        simp only [GridSegment.direction,GridSegment.reverse]; ring
      have y : (subdivisionSegment source drawing tagged.1).reverse.direction.2 = -(subdivisionSegment source drawing tagged.1).direction.2 := by
        simp only [GridSegment.direction,GridSegment.reverse]; ring
      simpa only [x,y,abs_neg] using bounds
    · intro vertical
      have sameX : (subdivisionSegment source drawing tagged.1).start.1 = (subdivisionSegment source drawing tagged.1).finish.1 := by
        change (subdivisionSegment source drawing tagged.1).reverse.direction.1 = 0 at vertical
        simp only [GridSegment.direction,GridSegment.reverse] at vertical
        omega
      have coordinates := vertical_anchoredSegment_x planar degree (Cubic.coreFactor drawing.gridSize) member sameX
      simpa only [incidentAnchoredSegment,ite_true,GridSegment.reverse,coordinates.1,coordinates.2,sameX]

theorem IncidentCoreData.translate {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    {port : GraphPort (Vertex V)} {raw core : GridSegment} (data : IncidentCoreData source drawing port raw core) (offset : Cell) :
    IncidentCoreData source drawing port (raw.translate offset)
      (core.translate (Cell.scale (Cubic.coreFactor drawing.gridSize) offset)) := by
  refine ⟨data.member,?_,?_,?_,?_,?_,?_⟩
  · simpa only [GridSegment.straightRayKey_translate] using data.key
  · intro equal
    have x := congrArg Prod.fst equal
    have y := congrArg Prod.snd equal
    apply data.genuine
    apply Prod.ext <;> simp only [GridSegment.translate,Cell.add] at x y <;> omega
  · simpa only [GridSegment.direction_translate] using data.bounds
  · change GridSegment.BoundedEndpointPerturbation 10 (Cubic.coreFactor drawing.gridSize) (raw.translate offset)
      (core.translate (Cell.scale (Cubic.coreFactor drawing.gridSize) offset))
    have cancel (first last shift : Int) : (Cubic.coreFactor drawing.gridSize : Int)*shift+first-
        (Cubic.coreFactor drawing.gridSize : Int)*(shift+last) = first-(Cubic.coreFactor drawing.gridSize : Int)*last := by ring
    simpa only [GridSegment.BoundedEndpointPerturbation,GridSegment.translate,Cell.add,Cell.scale,cancel] using data.perturbed
  · change Cell.add (Cell.scale (Cubic.coreFactor drawing.gridSize) offset) core.start =
      Cell.add (Cell.scale (Cubic.coreFactor drawing.gridSize) (Cell.add offset raw.start)) (fanAnchor source drawing port)
    rw [data.start]
    apply Prod.ext <;> simp only [GridSegment.translate,Cell.add,Cell.scale] <;> ring
  · intro vertical
    have equal := data.vertical (by simpa only [GridSegment.direction_translate] using vertical)
    simp only [GridSegment.translate,Cell.add,equal]

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
