/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendPorts
import LeanTrominoes.OrthogonalBendFanAssignment

/-! # Certified fan assignment on the raw bend subdivision

Original vertices use the degree-four rectangle templates. Inserted bends
use the sign-preserving two-ray templates, assigned from the actual ports
of the planar affine bookkeeping drawing.
-/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision PeriodicOrthocrossing OrthogonalDrawingRefinement

def bendFirstPort {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (edgeIndex pointIndex : Nat) : GraphPort (Vertex V) :=
  (portsAt (subdivisionGraph source drawing) (.bend edgeIndex pointIndex)).getD 0
    ⟨.bend edgeIndex pointIndex,0,.source⟩

def bendSecondPort {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (edgeIndex pointIndex : Nat) : GraphPort (Vertex V) :=
  (portsAt (subdivisionGraph source drawing) (.bend edgeIndex pointIndex)).getD 1
    ⟨.bend edgeIndex pointIndex,0,.source⟩

theorem bend_ports_eq {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    {edgeIndex pointIndex : Nat} (member : Vertex.bend edgeIndex pointIndex ∈ (subdivisionGraph source drawing).vertices) :
    portsAt (subdivisionGraph source drawing) (.bend edgeIndex pointIndex) =
      [bendFirstPort source drawing edgeIndex pointIndex,bendSecondPort source drawing edgeIndex pointIndex] := by
  obtain ⟨first,second,ports⟩ := List.length_eq_two.mp (bend_ports_length member)
  simp [bendFirstPort,bendSecondPort,ports]

theorem bend_keys_ne {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) {edgeIndex pointIndex : Nat}
    (member : Vertex.bend edgeIndex pointIndex ∈ (subdivisionGraph source drawing).vertices) :
    (shiftedDrawing source drawing).portRayKey (bendFirstPort source drawing edgeIndex pointIndex) ≠
      (shiftedDrawing source drawing).portRayKey (bendSecondPort source drawing edgeIndex pointIndex) := by
  have nodup := portRayKeys_nodup (shifted_distinctPortRayKeys planar) (.bend edgeIndex pointIndex)
  rw [bend_ports_eq member] at nodup
  simpa using nodup

def bendProfile {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (edgeIndex pointIndex : Nat) : BendFan.Profile :=
  BendFan.assignedProfile
    ((shiftedDrawing source drawing).portRayKey (bendFirstPort source drawing edgeIndex pointIndex))
    ((shiftedDrawing source drawing).portRayKey (bendSecondPort source drawing edgeIndex pointIndex))

theorem bendProfile_valid {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) {edgeIndex pointIndex : Nat}
    (member : Vertex.bend edgeIndex pointIndex ∈ (subdivisionGraph source drawing).vertices) :
    (bendProfile source drawing edgeIndex pointIndex).Valid :=
  BendFan.assignedProfile_valid (bend_keys_ne planar member)

def bendPortIndex {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (edgeIndex pointIndex : Nat) (port : GraphPort (Vertex V)) : Bool :=
  let index := BendFan.assignedIndex
    ((shiftedDrawing source drawing).portRayKey (bendFirstPort source drawing edgeIndex pointIndex))
    ((shiftedDrawing source drawing).portRayKey (bendSecondPort source drawing edgeIndex pointIndex))
  if port = bendFirstPort source drawing edgeIndex pointIndex then index else !index

def fanRoute {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (port : GraphPort (Vertex V)) : List Cell :=
  match port.vertex with
  | .original _ => incidenceTemplate (subdivisionGraph source drawing) (shiftedDrawing source drawing) port
  | .bend edgeIndex pointIndex =>
      (bendProfile source drawing edgeIndex pointIndex).route (bendPortIndex source drawing edgeIndex pointIndex port)

theorem fanRoute_head {V : Type*} [DecidableEq V] (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (port : GraphPort (Vertex V)) : (fanRoute source drawing port).head? = some (0,0) := by
  unfold fanRoute
  cases port.vertex
  · exact incidenceTemplate_head _ _ _
  · exact BendFan.route_head _ _

theorem fanRoute_orthogonal {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) {port : GraphPort (Vertex V)}
    (member : port ∈ allPorts (subdivisionGraph source drawing)) : OrthogonalPolyline (fanRoute source drawing port) := by
  have vertexMember := port_vertex_mem (subdivisionGraph_wellFormed planar.1.1.1 drawing) member
  unfold fanRoute
  cases vertex : port.vertex with
  | original value => exact incidenceTemplate_orthogonal _ _ _
  | bend edgeIndex pointIndex =>
      rw [vertex] at vertexMember
      exact BendFan.route_orthogonal _ _ (bendProfile_valid planar vertexMember)

theorem fanRoute_simple {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) {port : GraphPort (Vertex V)}
    (member : port ∈ allPorts (subdivisionGraph source drawing)) : GridPolyline.IsRealOpenSimple (fanRoute source drawing port) := by
  have vertexMember := port_vertex_mem (subdivisionGraph_wellFormed planar.1.1.1 drawing) member
  unfold fanRoute
  cases vertex : port.vertex with
  | original value => exact incidenceTemplate_isRealOpenSimple _ _ _
  | bend edgeIndex pointIndex =>
      rw [vertex] at vertexMember
      exact BendFan.route_simple _ _ (bendProfile_valid planar vertexMember)

theorem bendPortIndex_injective {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    {edgeIndex pointIndex : Nat} (vertexMember : Vertex.bend edgeIndex pointIndex ∈ (subdivisionGraph source drawing).vertices)
    {first second : GraphPort (Vertex V)}
    (firstMember : first ∈ portsAt (subdivisionGraph source drawing) (.bend edgeIndex pointIndex))
    (secondMember : second ∈ portsAt (subdivisionGraph source drawing) (.bend edgeIndex pointIndex))
    (equal : bendPortIndex source drawing edgeIndex pointIndex first = bendPortIndex source drawing edgeIndex pointIndex second) :
    first = second := by
  have nodup := portsAt_nodup (subdivisionGraph source drawing) (.bend edgeIndex pointIndex)
  rw [bend_ports_eq vertexMember] at firstMember secondMember nodup
  have different : bendFirstPort source drawing edgeIndex pointIndex ≠ bendSecondPort source drawing edgeIndex pointIndex := by
    simpa using nodup
  simp only [List.mem_cons,List.not_mem_nil,or_false] at firstMember secondMember
  rcases firstMember with rfl | rfl <;> rcases secondMember with rfl | rfl
  · rfl
  · simp [bendPortIndex,different.symm] at equal
  · simp [bendPortIndex,different.symm] at equal
  · rfl

theorem fanRoutes_contact {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (degree : source.DegreeAtMost 4)
    {first second : GraphPort (Vertex V)}
    (firstMember : first ∈ allPorts (subdivisionGraph source drawing))
    (secondMember : second ∈ allPorts (subdivisionGraph source drawing))
    (sameVertex : first.vertex = second.vertex) (different : first ≠ second) {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains (fanRoute source drawing first) point)
    (secondContains : GridPolyline.RealContains (fanRoute source drawing second) point) : point = realCell (0,0) := by
  have vertexMember := port_vertex_mem (subdivisionGraph_wellFormed planar.1.1.1 drawing) firstMember
  cases vertex : first.vertex with
  | original value =>
      simp only [fanRoute,vertex,← sameVertex] at firstContains secondContains
      exact incidenceTemplates_contact (shifted_distinctPortRayKeys planar)
        (subdivisionGraph_degreeAtMost degree (by decide) drawing)
        firstMember secondMember sameVertex different firstContains secondContains
  | bend edgeIndex pointIndex =>
      rw [vertex] at vertexMember
      have firstAt : first ∈ portsAt (subdivisionGraph source drawing) (.bend edgeIndex pointIndex) := by
        simpa only [vertex] using port_mem_portsAt (subdivisionGraph source drawing) firstMember
      have secondAt : second ∈ portsAt (subdivisionGraph source drawing) (.bend edgeIndex pointIndex) := by
        simpa only [← sameVertex,vertex] using port_mem_portsAt (subdivisionGraph source drawing) secondMember
      have distinct : bendPortIndex source drawing edgeIndex pointIndex first ≠ bendPortIndex source drawing edgeIndex pointIndex second :=
        fun equal => different (bendPortIndex_injective vertexMember firstAt secondAt equal)
      simp only [fanRoute,vertex,← sameVertex] at firstContains secondContains
      cases firstIndex : bendPortIndex source drawing edgeIndex pointIndex first <;>
        cases secondIndex : bendPortIndex source drawing edgeIndex pointIndex second
      · simp_all
      · exact BendFan.routes_contact _ (bendProfile_valid planar vertexMember)
          (by simpa only [firstIndex] using firstContains) (by simpa only [secondIndex] using secondContains)
      · exact BendFan.routes_contact _ (bendProfile_valid planar vertexMember)
          (by simpa only [secondIndex] using secondContains) (by simpa only [firstIndex] using firstContains)
      · simp_all

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
