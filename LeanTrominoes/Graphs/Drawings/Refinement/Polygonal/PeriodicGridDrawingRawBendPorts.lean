/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingRawBendSubdivisionPlanarity
import LeanTrominoes.Graphs.Drawings.Refinement.Straight.PeriodicGridDrawingStraightAnchorAssignment

/-! # Incidence ports for the raw bend subdivision

Inserted vertices have exactly two ports. The affine bookkeeping drawing
has distinct outward ray keys, so the existing degree-four anchor assignment
applies at original vertices without moving any bend.
-/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision PeriodicOrthocrossing

theorem bend_incidence_count {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    {edgeIndex pointIndex : Nat} (member : Vertex.bend edgeIndex pointIndex ∈ (subdivisionGraph source drawing).vertices) :
    (subdivisionGraph source drawing).incidences.count (.bend edgeIndex pointIndex) = 2 := by
  let bends := source.edges.zipIdx.flatMap fun edge => (middle drawing edge).map Prod.fst
  have bendMember : Vertex.bend edgeIndex pointIndex ∈ bends := by
    simp only [subdivisionGraph,graph,List.mem_append] at member
    rcases member with original | bend
    · obtain ⟨vertex,_,equal⟩ := List.mem_map.mp original
      cases equal
    · exact bend
  have positive := List.count_pos_iff.mpr bendMember
  have atMost := List.nodup_iff_count_le_one.mp (middle_indices_unique source drawing) (.bend edgeIndex pointIndex)
  change bends.count (.bend edgeIndex pointIndex) ≤ 1 at atMost
  have count : bends.count (.bend edgeIndex pointIndex) = 1 := by omega
  have zero : (source.incidences.map Vertex.original).count (.bend edgeIndex pointIndex) = 0 := by
    apply List.count_eq_zero.mpr
    simp
  change (graph source (middle drawing)).incidences.count (.bend edgeIndex pointIndex) = 2
  rw [incidence_count,zero,zero_add]
  change 2*bends.count (.bend edgeIndex pointIndex) = 2
  rw [count]

theorem bend_ports_length {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    {edgeIndex pointIndex : Nat} (member : Vertex.bend edgeIndex pointIndex ∈ (subdivisionGraph source drawing).vertices) :
    (portsAt (subdivisionGraph source drawing) (.bend edgeIndex pointIndex)).length = 2 := by
  rw [portsAt_length,bend_incidence_count member]

theorem shifted_distinctPortRayKeys {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) :
    (shiftedDrawing source drawing).DistinctPortRayKeys (subdivisionGraph source drawing) :=
  distinctPortRayKeys_of_planar_straight (shifted_planar planar) (fun _ member => shifted_straight source drawing member)

theorem shifted_anchor_degree_le_four {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4) (vertex : Vertex V) :
    (OrthogonalDrawingRefinement.vertexAnchorProfile (subdivisionGraph source drawing) (shiftedDrawing source drawing) vertex).degree ≤ 4 :=
  OrthogonalDrawingRefinement.vertexAnchorProfile_degree_le_four (shifted_distinctPortRayKeys planar)
    (subdivisionGraph_degreeAtMost degree (by decide) drawing) vertex

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
