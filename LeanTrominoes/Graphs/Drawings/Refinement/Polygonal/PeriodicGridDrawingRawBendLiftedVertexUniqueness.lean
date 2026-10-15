/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingRawBendLiftedIncidentCores
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRealLiftedVertices

/-! # Raw vertex copies and their endpoint incidences are uniquely positioned -/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem raw_lifted_vertex_eq {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) {first second : Vertex V}
    (firstMember : first ∈ (subdivisionGraph source drawing).vertices)
    (secondMember : second ∈ (subdivisionGraph source drawing).vertices) {firstCopy secondCopy : Cell}
    (equal : Cell.add (position source drawing first) (drawing.periodTranslation firstCopy) =
      Cell.add (position source drawing second) (drawing.periodTranslation secondCopy)) :
    first = second ∧ firstCopy = secondCopy := by
  apply (shifted_compatible planar).lifted_vertex_eq firstMember secondMember
  rw [shifted_vertexPosition_eq source drawing firstMember,shifted_vertexPosition_eq source drawing secondMember]
  have x := congrArg Prod.fst equal
  have y := congrArg Prod.snd equal
  apply Prod.ext <;>
    simp only [shiftedPosition,periodTranslation,shiftedDrawing_gridSize,Cell.add,Cell.scale,Nat.cast_mul,Nat.cast_ofNat] at x y ⊢ <;>
    nlinarith

def incidentCopy {V : Type*} (tagged : PeriodicEdge (Vertex V) × Nat) (target : Bool) (copy : Cell) : Cell :=
  if target then Cell.add tagged.1.offset copy else copy

theorem liftedIncidentRawSegment_start {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge (Vertex V) × Nat) (target : Bool) (copy : Cell) :
    (liftedIncidentRawSegment source drawing tagged target copy).start =
      Cell.add (position source drawing (incidentPort tagged target).vertex) (drawing.periodTranslation (incidentCopy tagged target copy)) := by
  cases target <;> apply Prod.ext <;>
    simp only [liftedIncidentRawSegment,incidentRawSegment,incidentPort,incidentCopy,ite_true,Bool.false_eq_true,ite_false,
      GridSegment.translate,GridSegment.reverse,subdivisionSegment,sourcePort,targetPort,Cell.add,Cell.scale,periodTranslation] <;> ring

theorem lifted_incident_start_unique {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source)
    {first second : PeriodicEdge (Vertex V) × Nat}
    (firstMember : first ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (secondMember : second ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (firstTarget secondTarget : Bool) (firstCopy secondCopy : Cell)
    (equal : (liftedIncidentRawSegment source drawing first firstTarget firstCopy).start =
      (liftedIncidentRawSegment source drawing second secondTarget secondCopy).start) :
    (incidentPort first firstTarget).vertex = (incidentPort second secondTarget).vertex ∧
      incidentCopy first firstTarget firstCopy = incidentCopy second secondTarget secondCopy := by
  have wellFormed := subdivisionGraph_wellFormed planar.1.1.1 drawing
  have firstPortMember : incidentPort first firstTarget ∈ allPorts (subdivisionGraph source drawing) := by
    cases firstTarget
    · exact sourcePort_mem_allPorts _ firstMember
    · exact targetPort_mem_allPorts _ firstMember
  have secondPortMember : incidentPort second secondTarget ∈ allPorts (subdivisionGraph source drawing) := by
    cases secondTarget
    · exact sourcePort_mem_allPorts _ secondMember
    · exact targetPort_mem_allPorts _ secondMember
  rw [liftedIncidentRawSegment_start,liftedIncidentRawSegment_start] at equal
  exact raw_lifted_vertex_eq planar (port_vertex_mem wellFormed firstPortMember) (port_vertex_mem wellFormed secondPortMember) equal

theorem lifted_incident_ports_ne {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source)
    {first second : PeriodicEdge (Vertex V) × Nat}
    (firstMember : first ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (secondMember : second ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (firstTarget secondTarget : Bool) (firstCopy secondCopy : Cell)
    (equal : (liftedIncidentRawSegment source drawing first firstTarget firstCopy).start =
      (liftedIncidentRawSegment source drawing second secondTarget secondCopy).start)
    (different : (first.2,firstCopy) ≠ (second.2,secondCopy)) :
    incidentPort first firstTarget ≠ incidentPort second secondTarget := by
  intro portsEqual
  have indices : first.2 = second.2 := by
    have indexEqual := congrArg GraphPort.edgeIndex portsEqual
    cases firstTarget <;> cases secondTarget <;> exact indexEqual
  have taggedEqual := tagged_eq_of_mem_zipIdx_of_snd_eq firstMember secondMember indices
  have targets : firstTarget = secondTarget := by
    have kindEqual := congrArg GraphPort.endKind portsEqual
    cases firstTarget <;> cases secondTarget <;> simp_all [incidentPort,sourcePort,targetPort]
  have copies := (lifted_incident_start_unique planar firstMember secondMember firstTarget secondTarget firstCopy secondCopy equal).2
  rw [← taggedEqual,← targets] at copies
  have copyEqual : firstCopy = secondCopy := by
    have x := congrArg Prod.fst copies
    have y := congrArg Prod.snd copies
    cases firstTarget <;> apply Prod.ext <;> simp only [incidentCopy,ite_true,Bool.false_eq_true,ite_false,Cell.add] at x y ⊢ <;> omega
  exact different (Prod.ext indices copyEqual)

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
