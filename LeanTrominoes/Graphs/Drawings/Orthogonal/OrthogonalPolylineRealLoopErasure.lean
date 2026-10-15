/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.OrthogonalPolylineLoopErasureSeparation
import LeanTrominoes.Common.Geometry.GridPolylineRealOpenSimple
import LeanTrominoes.Common.Geometry.GridSegmentRealConvexity
import LeanTrominoes.Common.Geometry.GridPolylineRealTube

/-! # Real simplicity and geometric bounds after loop erasure

A duplicate-free unit lattice path is simple in the real plane. Normalizing
an orthogonal walk also preserves any coordinate-tube bound on its complete
image. These facts allow digital routes to use the existing loop eraser.
-/
namespace LeanTrominoes
namespace AxisDirection

theorem IsUnitAxisStep.axisAligned {first last : Cell} (unit : IsUnitAxisStep first last) :
    (GridSegment.mk first last).IsAxisAligned := by
  obtain ⟨direction,genuine,rfl⟩ := unit
  rcases first with ⟨x,y⟩
  cases direction <;> simp_all [IsGenuine,step,Cell.add,GridSegment.IsAxisAligned,
    GridSegment.IsHorizontal,GridSegment.IsVertical]

theorem IsUnitAxisStep.contains_endpoint {first last point : Cell} (unit : IsUnitAxisStep first last)
    (contains : (GridSegment.mk first last).Contains point) : point = first ∨ point = last := by
  obtain ⟨direction,genuine,rfl⟩ := unit
  rcases first with ⟨x,y⟩
  rcases point with ⟨px,py⟩
  cases direction <;> simp_all [IsGenuine,step,Cell.add,GridSegment.Contains,
    GridSegment.IsHorizontal,GridSegment.IsVertical,GridSegment.Between,Prod.mk.injEq] <;> omega

theorem unit_steps_joint_box {first middle last : Cell}
    (firstUnit : IsUnitAxisStep first middle) (lastUnit : IsUnitAxisStep middle last)
    (different : first ≠ last) :
    GridSegment.BoxIntersectionIsPoint ⟨first,middle⟩ ⟨middle,last⟩ middle := by
  obtain ⟨firstDirection,firstGenuine,rfl⟩ := firstUnit
  obtain ⟨lastDirection,lastGenuine,rfl⟩ := lastUnit
  rcases first with ⟨x,y⟩
  cases firstDirection <;> cases lastDirection <;>
    simp_all [IsGenuine,step,Cell.add,GridSegment.BoxIntersectionIsPoint,Prod.mk.injEq]

private theorem nodup_lookup_indices {route : List Cell} (nodup : route.Nodup)
    {first second : Nat} {point : Cell}
    (firstAt : route[first]? = some point) (secondAt : route[second]? = some point) : first = second := by
  obtain ⟨firstValid,firstAt⟩ := List.getElem?_eq_some_iff.mp firstAt
  obtain ⟨secondValid,secondAt⟩ := List.getElem?_eq_some_iff.mp secondAt
  exact nodup.getElem_inj_iff.mp (firstAt.trans secondAt.symm)

theorem realOpenSimple_of_nodup_unitSteps {route : List Cell} (long : 2 ≤ route.length)
    (nodup : route.Nodup) (units : route.IsChain IsUnitAxisStep) : GridPolyline.IsRealOpenSimple route := by
  have segmentUnits := (unitSteps_iff_segments route).mp units
  refine ⟨long,fun piece member => (segmentUnits piece member).ne,?_⟩
  intro first firstMember second secondMember ordered point firstContains secondContains
  have firstUnit := segmentUnits first.1 (List.fst_mem_of_mem_zipIdx firstMember)
  have secondUnit := segmentUnits second.1 (List.fst_mem_of_mem_zipIdx secondMember)
  have firstEnds := indexed_gridPolylineSegment_endpoints firstMember
  have secondEnds := indexed_gridPolylineSegment_endpoints secondMember
  obtain ⟨witness,firstWitness,secondWitness⟩ :=
    GridSegment.real_intersection_has_integer_witness firstUnit.axisAligned secondUnit.axisAligned
      firstContains secondContains
  have consecutive : first.2+1 = second.2 := by
    rcases firstUnit.contains_endpoint firstWitness with equal | equal <;>
      rcases secondUnit.contains_endpoint secondWitness with otherEqual | otherEqual
    · have indices := nodup_lookup_indices nodup (firstEnds.1.trans (congrArg some equal.symm))
        (secondEnds.1.trans (congrArg some otherEqual.symm))
      omega
    · have indices := nodup_lookup_indices nodup (firstEnds.1.trans (congrArg some equal.symm))
        (secondEnds.2.trans (congrArg some otherEqual.symm))
      omega
    · exact nodup_lookup_indices nodup (firstEnds.2.trans (congrArg some equal.symm))
        (secondEnds.1.trans (congrArg some otherEqual.symm))
    · have indices := nodup_lookup_indices nodup (firstEnds.2.trans (congrArg some equal.symm))
        (secondEnds.2.trans (congrArg some otherEqual.symm))
      omega
  have boundary := indexed_gridPolylineSegments_consecutive firstMember secondMember consecutive
  have different : first.1.start ≠ second.1.finish := by
    intro equal
    have indices := nodup_lookup_indices nodup (firstEnds.1.trans (congrArg some equal)) secondEnds.2
    omega
  have certificate : GridSegment.BoxIntersectionIsPoint first.1 second.1 first.1.finish := by
    have certified := unit_steps_joint_box firstUnit (by simpa only [boundary] using secondUnit) different
    have firstEta : (⟨first.1.start,first.1.finish⟩ : GridSegment) = first.1 := by cases first.1; rfl
    have secondEta : (⟨first.1.finish,second.1.finish⟩ : GridSegment) = second.1 := by
      rw [boundary]
    simpa only [firstEta,secondEta] using certified
  exact ⟨consecutive,GridSegment.real_intersection_eq_of_box_certificate certificate firstContains secondContains⟩

theorem normalizeOrthogonalPolyline_realContains {route : List Cell}
    (nonempty : route ≠ []) (orthogonal : PeriodicOrthocrossing.OrthogonalPolyline route)
    {point : ℝ × ℝ} (contains : GridPolyline.RealContains (normalizeOrthogonalPolyline route) point) :
    GridPolyline.RealContains route point := by
  obtain ⟨piece,member,contains⟩ := contains
  have unitMember := (normalizeOrthogonalPolyline_segments_sublist_unitSubdividePolyline nonempty orthogonal).subset member
  obtain ⟨parent,parentMember,start,finish⟩ := unitSubdividePolyline_segment_provenance orthogonal unitMember
  exact ⟨parent,parentMember,GridSegment.realContains_of_endpoints_contained
    (GridSegment.realContains_of_contains start) (GridSegment.realContains_of_contains finish) contains⟩

theorem normalizeOrthogonalPolyline_tube {route : List Cell} {segment : GridSegment} {radius : ℝ}
    (nonempty : route ≠ []) (orthogonal : PeriodicOrthocrossing.OrthogonalPolyline route)
    (bound : ∀ point, GridPolyline.RealContains route point → segment.RealTubeContains radius point)
    {point : ℝ × ℝ} (contains : GridPolyline.RealContains (normalizeOrthogonalPolyline route) point) :
    segment.RealTubeContains radius point :=
  bound point (normalizeOrthogonalPolyline_realContains nonempty orthogonal contains)

theorem normalizeOrthogonalPolyline_realOpenSimple {route : List Cell} {first last : Cell}
    (nonempty : route ≠ []) (orthogonal : PeriodicOrthocrossing.OrthogonalPolyline route)
    (head : route.head? = some first) (tail : route.getLast? = some last) (different : first ≠ last) :
    GridPolyline.IsRealOpenSimple (normalizeOrthogonalPolyline route) := by
  have normalizedHead := (normalizeOrthogonalPolyline_head? nonempty orthogonal).trans head
  have normalizedLast := (normalizeOrthogonalPolyline_getLast? nonempty orthogonal).trans tail
  have long : 2 ≤ (normalizeOrthogonalPolyline route).length := by
    cases normalized : normalizeOrthogonalPolyline route with
    | nil => simp [normalized] at normalizedHead
    | cons point rest =>
        cases rest with
        | nil => simp_all
        | cons second rest => simp
  rw [normalizeOrthogonalPolyline_eq_erase nonempty orthogonal] at long ⊢
  exact realOpenSimple_of_nodup_unitSteps long (eraseOrthogonalLoops_nodup nonempty orthogonal)
    (eraseOrthogonalLoops_unitSteps nonempty orthogonal)

end AxisDirection
end LeanTrominoes
