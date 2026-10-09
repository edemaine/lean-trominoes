/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingBendPerturbationEndpointAgreement
import LeanTrominoes.PeriodicGridDrawingBendPerturbationSimplicity

/-! # Moved polygonal routes meet only at their graph endpoints -/
namespace LeanTrominoes.PeriodicGridDrawing.InteriorBends

private theorem translated_nonconstant {segment : GridSegment} (nonconstant : segment.start≠segment.finish)
    (offset : Cell) : (segment.translate offset).start≠(segment.translate offset).finish := by
  intro equal
  have x := congrArg Prod.fst equal
  have y := congrArg Prod.snd equal
  apply nonconstant
  apply Prod.ext <;> simp only [GridSegment.translate,Cell.add] at x y ⊢ <;> omega

theorem polygonal_direction_bounds_of_index {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    {index : Nat} (valid : index<drawing.edgeRoutes.length) {segment : GridSegment}
    (member : segment∈gridPolylineSegments (drawing.edgeRoute index)) :
    |segment.direction.1|≤2*(drawing.gridSize:Int) ∧ |segment.direction.2|≤2*(drawing.gridSize:Int) := by
  obtain ⟨tagged,taggedMember,lookup⟩ := tagged_edge_of_route_mem planar.1.1 (edgeRoute_mem_of_lt valid)
  rw [← lookup] at member
  exact polygonal_segment_direction_bounds planar localDrawing localGraph taggedMember member

theorem perturbDrawing_routesMeetOnlyAtEndpoints {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    {factor : Nat} (spacing : 16*(drawing.gridSize:Int)+8<(factor:Int)) :
    (perturbDrawing drawing factor).RealRoutesMeetOnlyAtEndpoints := by
  intro firstIndex secondIndex firstCell secondCell firstValid secondValid different p firstContains secondContains
  have gridPositive : (0:Int)<drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have positive : 0<factor := by omega
  have firstValid : firstIndex<drawing.edgeRoutes.length := by
    simpa only [perturbDrawing,List.length_map] using firstValid
  have secondValid : secondIndex<drawing.edgeRoutes.length := by
    simpa only [perturbDrawing,List.length_map] using secondValid
  obtain ⟨first,firstMember,firstOutputContains⟩ := moved_segment_provenance positive firstContains
  obtain ⟨second,secondMember,secondOutputContains⟩ := moved_segment_provenance positive secondContains
  have firstNonconstant := (planar.1.2.1 _ (edgeRoute_mem_of_lt firstValid)).2.1 first firstMember
  have secondNonconstant := (planar.1.2.1 _ (edgeRoute_mem_of_lt secondValid)).2.1 second secondMember
  have firstBounds := polygonal_direction_bounds_of_index planar localDrawing localGraph firstValid firstMember
  have secondBounds := polygonal_direction_bounds_of_index planar localDrawing localGraph secondValid secondMember
  have firstLiftedBounds : |(first.translate (drawing.periodTranslation firstCell)).direction.1|≤2*(drawing.gridSize:Int) ∧
      |(first.translate (drawing.periodTranslation firstCell)).direction.2|≤2*(drawing.gridSize:Int) := by
    simpa only [GridSegment.direction_translate] using firstBounds
  have secondLiftedBounds : |(second.translate (drawing.periodTranslation secondCell)).direction.1|≤2*(drawing.gridSize:Int) ∧
      |(second.translate (drawing.periodTranslation secondCell)).direction.2|≤2*(drawing.gridSize:Int) := by
    simpa only [GridSegment.direction_translate] using secondBounds
  obtain ⟨a,b,same,atFirst,atSecond⟩ := GridSegment.perturbations_contact
    (factor := (factor:Int)) (bound := 2*(drawing.gridSize:Int)) (by omega) (by omega)
    (translated_nonconstant firstNonconstant _) (translated_nonconstant secondNonconstant _)
    firstLiftedBounds secondLiftedBounds
    (lifted_endpoint_contacts planar firstValid secondValid firstCell secondCell different firstMember secondMember)
    (moved_lifted_segment_perturbed drawing factor first firstCell)
    (moved_lifted_segment_perturbed drawing factor second secondCell)
    (lifted_endpoint_agreement planar firstValid secondValid firstCell secondCell different firstMember secondMember factor)
    firstOutputContains secondOutputContains
  let q := ((first.translate (drawing.periodTranslation firstCell)).oriented a).start
  have firstOld : (first.translate (drawing.periodTranslation firstCell)).RealContains (realCell q) :=
    (GridSegment.oriented_contains _ _ _).mp (GridSegment.realContains_start _)
  have secondOld : (second.translate (drawing.periodTranslation secondCell)).RealContains (realCell q) := by
    rw [show q=((second.translate (drawing.periodTranslation secondCell)).oriented b).start from same]
    exact (GridSegment.oriented_contains _ _ _).mp (GridSegment.realContains_start _)
  have endpoints := planar.2 firstIndex secondIndex firstCell secondCell firstValid secondValid different (realCell q)
    (lifted_segment_in_route firstMember firstOld) (lifted_segment_in_route secondMember secondOld)
  have firstEndpoint := lifted_endpoint_transport positive (by
    simpa only [q,translated_oriented_start] using endpoints.1)
  have secondEndpoint := lifted_endpoint_transport positive (by
    rw [show q=((second.translate (drawing.periodTranslation secondCell)).oriented b).start from same] at endpoints
    simpa only [translated_oriented_start] using endpoints.2)
  rw [GridSegment.mapPoints_oriented_start] at atFirst atSecond
  exact ⟨by simpa only [atFirst] using firstEndpoint,by simpa only [atSecond] using secondEndpoint⟩

end LeanTrominoes.PeriodicGridDrawing.InteriorBends
