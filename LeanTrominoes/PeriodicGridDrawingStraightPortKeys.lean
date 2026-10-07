/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingStraightEndpointRays

/-! # Planar straight-edge drawings have distinct incidence ray keys -/
namespace LeanTrominoes

namespace GridSegment

theorem rationalSlope_translate (segment : GridSegment) (offset : Cell) :
    (segment.translate offset).rationalSlope = segment.rationalSlope := by
  simp [rationalSlope,translate,Cell.add]

theorem straightRayKey_translate (segment : GridSegment) (offset : Cell) :
    (segment.translate offset).straightRayKey = segment.straightRayKey := by
  unfold straightRayKey
  rw [rationalSlope_translate]
  simp [translate,Cell.add]

end GridSegment

namespace PeriodicGridDrawing
open PeriodicOrthocrossing GeneralVertexNormalization

def portRayKey (drawing : PeriodicGridDrawing) {Vertex : Type*} (port : GraphPort Vertex) : StraightRayKey :=
  match port.endKind with
  | .source => (drawing.straightSegment port.edgeIndex).straightRayKey
  | .target => (drawing.straightSegment port.edgeIndex).reverse.straightRayKey

theorem outwardStraightSegment_key {Vertex : Type*} (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge Vertex × Nat) (target : Bool) :
    (drawing.outwardStraightSegment tagged target).straightRayKey =
      drawing.portRayKey (endpointPort tagged target) := by
  cases target
  · exact GridSegment.straightRayKey_translate _ _
  · change ((drawing.straightSegment tagged.2).translate _).reverse.straightRayKey = _
    have commutes : ((drawing.straightSegment tagged.2).translate
        (drawing.periodTranslation (endpointCell tagged true))).reverse =
        (drawing.straightSegment tagged.2).reverse.translate
          (drawing.periodTranslation (endpointCell tagged true)) := rfl
    rw [commutes,GridSegment.straightRayKey_translate]
    rfl

theorem endpoint_same_key_eq {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    {a b : PeriodicEdge Vertex × Nat} (am : a ∈ graph.edges.zipIdx) (bm : b ∈ graph.edges.zipIdx)
    (aStraight : (drawing.edgeRoute a.2).length = 2) (bStraight : (drawing.edgeRoute b.2).length = 2)
    (aTarget bTarget : Bool) (sameVertex : (endpointPort a aTarget).vertex = (endpointPort b bTarget).vertex)
    (sameKey : drawing.portRayKey (endpointPort a aTarget) = drawing.portRayKey (endpointPort b bTarget)) :
    endpointPort a aTarget = endpointPort b bTarget := by
  have actualKeys : (drawing.outwardStraightSegment a aTarget).straightRayKey =
      (drawing.outwardStraightSegment b bTarget).straightRayKey := by
    rw [outwardStraightSegment_key,outwardStraightSegment_key]
    exact sameKey
  have occurrences := outwardStraightSegment_same_key_same_occurrence planar am bm aStraight bStraight
    aTarget bTarget sameVertex actualKeys
  have indices : a.2 = b.2 := congrArg Prod.fst occurrences
  have firstAt := List.mem_zipIdx_iff_getElem?.mp am
  have secondAt := List.mem_zipIdx_iff_getElem?.mp bm
  rw [← indices] at secondAt
  have edges := Option.some.inj (firstAt.symm.trans secondAt)
  have tags : a = b := Prod.ext edges indices
  subst b
  have nondegenerate := straightSegment_nondegenerate planar.1 am aStraight
  cases aTarget <;> cases bTarget
  · rfl
  · exact (GridSegment.straightRayKey_reverse_ne nondegenerate sameKey).elim
  · exact (GridSegment.straightRayKey_reverse_ne nondegenerate sameKey.symm).elim
  · rfl

def DistinctPortRayKeys {Vertex : Type*} (drawing : PeriodicGridDrawing) (graph : PeriodicGraph Vertex) : Prop :=
  ∀ first ∈ allPorts graph, ∀ second ∈ allPorts graph,
    first.vertex = second.vertex → drawing.portRayKey first = drawing.portRayKey second → first = second

theorem distinctPortRayKeys_of_planar_straight {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2) :
    drawing.DistinctPortRayKeys graph := by
  intro first firstMember second secondMember sameVertex sameKey
  obtain ⟨a,am,firstKind⟩ := allPorts_has_edge firstMember
  obtain ⟨b,bm,secondKind⟩ := allPorts_has_edge secondMember
  rcases firstKind with rfl | rfl <;> rcases secondKind with rfl | rfl
  · exact endpoint_same_key_eq planar am bm (straight a am) (straight b bm) false false sameVertex sameKey
  · exact endpoint_same_key_eq planar am bm (straight a am) (straight b bm) false true sameVertex sameKey
  · exact endpoint_same_key_eq planar am bm (straight a am) (straight b bm) true false sameVertex sameKey
  · exact endpoint_same_key_eq planar am bm (straight a am) (straight b bm) true true sameVertex sameKey

theorem portRayKeys_nodup {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (distinct : drawing.DistinctPortRayKeys graph) (vertex : Vertex) :
    ((portsAt graph vertex).map drawing.portRayKey).Nodup := by
  apply List.Nodup.map_on ?_ (portsAt_nodup graph vertex)
  intro first firstMember second secondMember equal
  have firstData : first ∈ allPorts graph ∧ first.vertex = vertex := by simpa [portsAt] using firstMember
  have secondData : second ∈ allPorts graph ∧ second.vertex = vertex := by simpa [portsAt] using secondMember
  exact distinct first firstData.1 second secondData.1 (firstData.2.trans secondData.2.symm) equal

end PeriodicGridDrawing
end LeanTrominoes
