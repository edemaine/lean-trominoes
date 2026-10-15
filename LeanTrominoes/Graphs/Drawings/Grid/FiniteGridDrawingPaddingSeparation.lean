/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.FiniteGridDrawingPaddingPlanarity
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingPointBounds
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingLiftedInteriorContactSeparation
import LeanTrominoes.Graphs.Drawings.Orthogonal.OrthogonalPolylineTailReplacementSeparation

/-! # Complete route separation after finite padding -/
namespace LeanTrominoes.PeriodicGridDrawing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

private theorem indexed_of_segment_mem {drawing : PeriodicGridDrawing}
    {route : List Cell} {index : Nat} (routeMember : (route,index)∈drawing.edgeRoutes.zipIdx)
    {segment : GridSegment} (member : segment∈gridPolylineSegments route) :
    ∃ indexed∈drawing.indexedSegments,indexed.segment=segment := by
  obtain ⟨segmentIndex,rfl⟩ := List.mem_iff_get.mp member
  exact ⟨⟨index,segmentIndex,(gridPolylineSegments route).get segmentIndex⟩,
    indexedSegment_mem_of_route_mem routeMember segmentIndex,rfl⟩

private theorem point_translate_zero {drawing : PeriodicGridDrawing} {first second shift : Cell}
    (firstInside : drawing.PositionInFundamentalSquare first)
    (secondInside : drawing.PositionInFundamentalSquare second)
    (eq : first=Cell.add (drawing.periodTranslation shift) second) : shift=(0,0) := by
  have positive : (0:Int)<drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  apply Prod.ext
  · exact PeriodicOrthocrossing.finite_lane_shift_zero positive
      (le_of_lt secondInside.1) secondInside.2.1 (le_of_lt firstInside.1) firstInside.2.1
      (by simpa [Cell.add,periodTranslation,Cell.scale,add_comm] using congrArg Prod.fst eq)
  · exact PeriodicOrthocrossing.finite_lane_shift_zero positive
      (le_of_lt secondInside.2.2.1) secondInside.2.2.2
      (le_of_lt firstInside.2.2.1) firstInside.2.2.2
      (by simpa [Cell.add,periodTranslation,Cell.scale,add_comm] using congrArg Prod.snd eq)

/-- Routes strictly inside one square cannot touch a different periodic copy. -/
theorem routesAvoidEachOther_of_nonzero_translate {drawing : PeriodicGridDrawing}
    (inside : drawing.RoutePointsInFundamentalSquare)
    {first second : List Cell} {firstIndex secondIndex : Nat}
    (firstMember : (first,firstIndex)∈drawing.edgeRoutes.zipIdx)
    (secondMember : (second,secondIndex)∈drawing.edgeRoutes.zipIdx)
    {shift : Cell} (nonzero : shift≠(0,0)) :
    RoutesAvoidEachOther first (second.map (Cell.add (drawing.periodTranslation shift))) := by
  have endpoints := segmentEndpointsInFundamentalSquare_of_routePoints inside
  have firstRouteMember := List.fst_mem_of_mem_zipIdx firstMember
  have secondRouteMember := List.fst_mem_of_mem_zipIdx secondMember
  apply routesAvoidEachOther_of_mem
  · intro firstSegment firstSegmentMember translatedSegment translatedMember meet
    rw [gridPolylineSegments_map_add] at translatedMember
    obtain ⟨secondSegment,secondSegmentMember,rfl⟩ := List.mem_map.mp translatedMember
    obtain ⟨firstIndexed,firstIndexedMember,firstEq⟩ := indexed_of_segment_mem firstMember firstSegmentMember
    obtain ⟨secondIndexed,secondIndexedMember,secondEq⟩ := indexed_of_segment_mem secondMember secondSegmentMember
    apply nonzero
    have translatedMeet : GridSegment.InteriorsMeet
        (secondIndexed.segment.translate (drawing.periodTranslation shift))
        (firstIndexed.segment.translate (drawing.periodTranslation (0,0))) := by
      rw [firstEq,secondEq]
      simpa [periodTranslation,Cell.scale,GridSegment.translate,Cell.add] using
        (GridSegment.interiorsMeet_comm _ _).mp meet
    simpa [Cell.sub] using relativeTranslate_eq_zero_of_interiorsMeet endpoints
      secondIndexedMember firstIndexedMember translatedMeet
  · intro point pointMember translatedSegment translatedMember contains
    rw [gridPolylineSegments_map_add] at translatedMember
    obtain ⟨segment,segmentMember,rfl⟩ := List.mem_map.mp translatedMember
    obtain ⟨indexed,indexedMember,indexedEq⟩ := indexed_of_segment_mem secondMember segmentMember
    apply nonzero
    apply occurrence_translate_eq_zero_of_contact (endpoints indexed indexedMember)
      (inside first firstRouteMember point pointMember)
    rwa [indexedEq]
  · intro translatedPoint translatedMember segment segmentMember contains
    obtain ⟨point,pointMember,rfl⟩ := List.mem_map.mp translatedMember
    obtain ⟨indexed,indexedMember,indexedEq⟩ := indexed_of_segment_mem firstMember segmentMember
    have normalized : (indexed.segment.translate
        (drawing.periodTranslation (Cell.sub (0,0) shift))).InteriorContains point := by
      have base : (indexed.segment.translate (drawing.periodTranslation (0,0))).InteriorContains
          (Cell.add point (drawing.periodTranslation shift)) := by
        rw [indexedEq]
        simpa [periodTranslation,Cell.scale,GridSegment.translate,Cell.add,add_comm] using contains
      simpa [normalizePoint,Cell.add,Cell.sub] using
        (interiorContains_normalize drawing indexed.segment (0,0) shift
          (Cell.add point (drawing.periodTranslation shift))).mp base
    have zero := occurrence_translate_eq_zero_of_contact (endpoints indexed indexedMember)
      (inside second secondRouteMember point pointMember) normalized
    apply nonzero
    apply Prod.ext <;> have eq := congrArg (fun p : Cell => p.1) zero
    · simp only [Cell.sub] at eq; omega
    · have eqY := congrArg Prod.snd zero; simp only [Cell.sub] at eqY; omega
  · intro point pointMember translatedPoint translatedMember eq
    obtain ⟨secondPoint,secondPointMember,rfl⟩ := List.mem_map.mp translatedMember
    exact False.elim (nonzero (point_translate_zero
      (inside first firstRouteMember point pointMember)
      (inside second secondRouteMember secondPoint secondPointMember) eq))

/-- Translating every stored route preserves its simplicity. -/
theorem finitePad_routesSimple {drawing : PeriodicGridDrawing}
    (simple : ∀ route∈drawing.edgeRoutes,LocalIncidenceDrawing.RouteIsSimple route) :
    ∀ route∈drawing.finitePad.edgeRoutes,LocalIncidenceDrawing.RouteIsSimple route := by
  intro route member
  obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
  exact routeIsSimple_translate (simple original originalMember) drawing.finitePaddingOffset

/-- Padding changes the period, but complete route separation is preserved
when all padded route points fit strictly inside the new square. -/
theorem finitePad_liftedRoutesAvoidEachOther {drawing : PeriodicGridDrawing}
    (inside : drawing.finitePad.RoutePointsInFundamentalSquare)
    (separated : drawing.LiftedRoutesAvoidEachOther) :
    drawing.finitePad.LiftedRoutesAvoidEachOther := by
  apply (liftedRoutesAvoidEachOther_iff_relative _).mpr
  intro first firstMember second secondMember shift different
  by_cases zero : shift=(0,0)
  · subst shift
    rw [map_add_periodTranslation_zero]
    simp only [finitePad,List.zipIdx_map,List.mem_map] at firstMember secondMember
    obtain ⟨originalFirst,originalFirstMember,rfl⟩ := firstMember
    obtain ⟨originalSecond,originalSecondMember,rfl⟩ := secondMember
    have originalDifferent : (originalFirst.2,((0,0):Cell))≠(originalSecond.2,((0,0):Cell)) := by
      simpa using different
    have avoids := separated originalFirst originalFirstMember originalSecond originalSecondMember
      (0,0) (0,0) originalDifferent
    rw [map_add_periodTranslation_zero,map_add_periodTranslation_zero] at avoids
    exact routesAvoidEachOther_translate avoids drawing.finitePaddingOffset
  · exact routesAvoidEachOther_of_nonzero_translate inside firstMember secondMember zero
end LeanTrominoes.PeriodicGridDrawing
