/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Refinement.Straight.PeriodicGridDrawingStraightPortKeys
import LeanTrominoes.Graphs.Drawings.Grid.OrthogonalVertexAnchorAssignment
import LeanTrominoes.Graphs.Drawings.Grid.OrthogonalVertexAnchorTemplateContacts
import LeanTrominoes.Graphs.Drawings.Grid.OrthogonalVertexAnchorTemplateDirections

/-! # Executable rectangle connector assignments for a planar straight drawing -/
namespace LeanTrominoes.OrthogonalDrawingRefinement
open PeriodicOrthocrossing

def vertexAnchorProfile {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (drawing : PeriodicGridDrawing) (vertex : Vertex) : AnchorProfile :=
  anchorProfileOfKeys ((portsAt graph vertex).map drawing.portRayKey)

def orderedIncidences {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (drawing : PeriodicGridDrawing) (vertex : Vertex) : List (GraphPort Vertex) :=
  (portsAt graph vertex).mergeSort
    (fun first second => decide ((drawing.portRayKey first).clockwiseCode ≤ (drawing.portRayKey second).clockwiseCode))

def incidenceAnchorIndex {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (drawing : PeriodicGridDrawing) (port : GraphPort Vertex) : Fin 4 :=
  ⟨(orderedIncidences graph drawing port.vertex).idxOf port % 4,Nat.mod_lt _ (by decide)⟩

def incidenceTemplate {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (drawing : PeriodicGridDrawing) (port : GraphPort Vertex) : List Cell :=
  rectangleTemplate (vertexAnchorProfile graph drawing port.vertex) (incidenceAnchorIndex graph drawing port)

theorem vertexAnchorProfile_degree {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (distinct : drawing.DistinctPortRayKeys graph)
    (degree : graph.DegreeAtMost 4) (vertex : Vertex) :
    (vertexAnchorProfile graph drawing vertex).degree = (portsAt graph vertex).length := by
  apply (anchorProfileOfKeys_degree (drawing.portRayKeys_nodup distinct vertex) ?_).trans (List.length_map ..)
  simpa [portsAt_length] using degree vertex

theorem vertexAnchorProfile_degree_le_four {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (distinct : drawing.DistinctPortRayKeys graph)
    (degree : graph.DegreeAtMost 4) (vertex : Vertex) :
    (vertexAnchorProfile graph drawing vertex).degree ≤ 4 := by
  rw [vertexAnchorProfile_degree distinct degree,portsAt_length]
  exact degree vertex

theorem orderedIncidences_perm {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (drawing : PeriodicGridDrawing) (vertex : Vertex) :
    (orderedIncidences graph drawing vertex).Perm (portsAt graph vertex) := List.mergeSort_perm _ _

theorem orderedIncidences_mem {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (drawing : PeriodicGridDrawing) (vertex : Vertex) (port : GraphPort Vertex) :
    port ∈ orderedIncidences graph drawing vertex ↔ port ∈ allPorts graph ∧ port.vertex = vertex := by
  rw [(orderedIncidences_perm graph drawing vertex).mem_iff]
  simp [portsAt]

theorem orderedIncidences_ordered {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (drawing : PeriodicGridDrawing) (vertex : Vertex) :
    (orderedIncidences graph drawing vertex).Pairwise
      (fun first second => (drawing.portRayKey first).clockwiseCode ≤ (drawing.portRayKey second).clockwiseCode) := by
  have ordered := List.pairwise_mergeSort
    (le := fun first second : GraphPort Vertex =>
      decide ((drawing.portRayKey first).clockwiseCode ≤ (drawing.portRayKey second).clockwiseCode))
    (by intro first second third h1 h2; simp only [decide_eq_true_eq] at *; exact le_trans h1 h2)
    (by intro first second; simp only [Bool.or_eq_true,decide_eq_true_eq]; exact le_total _ _) (portsAt graph vertex)
  simpa [orderedIncidences] using ordered

theorem incidenceAnchorIndex_val_eq {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (degree : graph.DegreeAtMost 4) {port : GraphPort Vertex}
    (member : port ∈ allPorts graph) :
    (incidenceAnchorIndex graph drawing port).val = (orderedIncidences graph drawing port.vertex).idxOf port := by
  have inside := (orderedIncidences_mem graph drawing port.vertex port).mpr ⟨member,rfl⟩
  have rank := List.idxOf_lt_length_iff.mpr inside
  have long := (orderedIncidences_perm graph drawing port.vertex).length_eq
  have bound : (portsAt graph port.vertex).length ≤ 4 := by simpa [portsAt_length] using degree port.vertex
  exact Nat.mod_eq_of_lt (by omega)

theorem incidenceAnchorIndex_valid {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (distinct : drawing.DistinctPortRayKeys graph)
    (degree : graph.DegreeAtMost 4) {port : GraphPort Vertex} (member : port ∈ allPorts graph) :
    (incidenceAnchorIndex graph drawing port).val < (vertexAnchorProfile graph drawing port.vertex).degree := by
  rw [incidenceAnchorIndex_val_eq degree member,vertexAnchorProfile_degree distinct degree,
    ← (orderedIncidences_perm graph drawing port.vertex).length_eq]
  exact List.idxOf_lt_length_iff.mpr ((orderedIncidences_mem graph drawing port.vertex port).mpr ⟨member,rfl⟩)

theorem incidenceAnchorIndex_injective {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (degree : graph.DegreeAtMost 4) {first second : GraphPort Vertex}
    (firstMember : first ∈ allPorts graph) (secondMember : second ∈ allPorts graph) (sameVertex : first.vertex = second.vertex)
    (equal : incidenceAnchorIndex graph drawing first = incidenceAnchorIndex graph drawing second) : first = second := by
  have ranks := congrArg Fin.val equal
  rw [incidenceAnchorIndex_val_eq degree firstMember,incidenceAnchorIndex_val_eq degree secondMember,← sameVertex] at ranks
  exact (List.idxOf_inj ((orderedIncidences_mem graph drawing first.vertex first).mpr ⟨firstMember,rfl⟩)).mp ranks

theorem incidenceTemplate_head {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (drawing : PeriodicGridDrawing) (port : GraphPort Vertex) : (incidenceTemplate graph drawing port).head? = some (0,0) :=
  rectangleTemplate_head _ _

theorem incidenceTemplate_last {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (distinct : drawing.DistinctPortRayKeys graph)
    (degree : graph.DegreeAtMost 4) {port : GraphPort Vertex} (member : port ∈ allPorts graph) :
    (incidenceTemplate graph drawing port).getLast? =
      (vertexAnchorProfile graph drawing port.vertex).anchors[(incidenceAnchorIndex graph drawing port).val]? :=
  rectangleTemplate_last _ _ (vertexAnchorProfile_degree_le_four distinct degree _)
    (incidenceAnchorIndex_valid distinct degree member)

theorem incidenceTemplate_isRealOpenSimple {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (drawing : PeriodicGridDrawing) (port : GraphPort Vertex) : GridPolyline.IsRealOpenSimple (incidenceTemplate graph drawing port) :=
  rectangleTemplate_isRealOpenSimple _ _

theorem incidenceTemplate_orthogonal {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (drawing : PeriodicGridDrawing) (port : GraphPort Vertex) : OrthogonalPolyline (incidenceTemplate graph drawing port) :=
  rectangleTemplate_orthogonal _ _

theorem incidenceTemplates_contact {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (distinct : drawing.DistinctPortRayKeys graph) (degree : graph.DegreeAtMost 4)
    {first second : GraphPort Vertex} (firstMember : first ∈ allPorts graph) (secondMember : second ∈ allPorts graph)
    (sameVertex : first.vertex = second.vertex) (different : first ≠ second) {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains (incidenceTemplate graph drawing first) point)
    (secondContains : GridPolyline.RealContains (incidenceTemplate graph drawing second) point) : point = realCell (0,0) := by
  have secondValid := incidenceAnchorIndex_valid distinct degree secondMember
  rw [← sameVertex] at secondValid
  have differentIndices : incidenceAnchorIndex graph drawing first ≠ incidenceAnchorIndex graph drawing second :=
    fun equal => different (incidenceAnchorIndex_injective degree firstMember secondMember sameVertex equal)
  apply rectangleTemplate_contacts_center _ _ _ (vertexAnchorProfile_degree_le_four distinct degree _)
    (incidenceAnchorIndex_valid distinct degree firstMember) secondValid differentIndices firstContains
  simpa only [incidenceTemplate,← sameVertex] using secondContains

end LeanTrominoes.OrthogonalDrawingRefinement
