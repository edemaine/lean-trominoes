import LeanTrominoes.OrthogonalPolylineUnitSubdivisionContacts
import LeanTrominoes.OrthogonalPolylineRouteReversalContacts
import LeanTrominoes.PeriodicGridDrawingRouteSimplicity

/-!
# Simplicity under unit subdivision

Replacing each segment of a simple orthogonal lattice polyline by its
ordered unit steps introduces no duplicate points.  This is the route-level
simplicity fact needed before assembling a positive-width ribbon.
-/

namespace LeanTrominoes

/-- A polyline with no repeated listed points also has no repeated directed
segment records. -/
theorem gridPolylineSegments_nodup_of_points_nodup
    {points : List Cell} (nodup : points.Nodup) :
    (gridPolylineSegments points).Nodup := by
  induction points using List.twoStepInduction with
  | nil | singleton =>
      simp [gridPolylineSegments]
  | cons_cons first second rest _ tailInduction =>
      rw [gridPolylineSegments]
      apply List.nodup_cons.mpr
      constructor
      · intro headMember
        have endpointMember :=
          gridPolylineSegments_endpoints_mem headMember
        exact (List.nodup_cons.mp nodup).1 endpointMember.1
      · exact tailInduction second nodup.tail

/-- Every segment of a route tail is also a segment of the full route. -/
theorem gridPolylineSegments_tail_subset
    (points : List Cell) :
    ∀ ⦃segment⦄,
      segment ∈ gridPolylineSegments points.tail →
        segment ∈ gridPolylineSegments points := by
  intro segment member
  cases points with
  | nil =>
      simp [gridPolylineSegments] at member
  | cons first rest =>
      cases rest with
      | nil =>
          simp [gridPolylineSegments] at member
      | cons second rest =>
          exact List.mem_cons_of_mem _ member

namespace LocalIncidenceDrawing

/-- Membership form of the distinct-segment clause in `RouteIsSimple`. -/
theorem RouteIsSimple.segmentInteriorsAvoid_of_mem
    {route : List Cell}
    (simple : RouteIsSimple route)
    {first second : GridSegment}
    (firstMember : first ∈ gridPolylineSegments route)
    (secondMember : second ∈ gridPolylineSegments route)
    (segmentsDifferent : first ≠ second) :
    ¬GridSegment.InteriorsMeet first second := by
  rcases List.mem_iff_get.mp firstMember with
    ⟨firstIndex, firstEquation⟩
  rcases List.mem_iff_get.mp secondMember with
    ⟨secondIndex, secondEquation⟩
  have indicesDifferent :
      firstIndex.val ≠ secondIndex.val := by
    intro equal
    apply segmentsDifferent
    calc
      first =
          (gridPolylineSegments route).get firstIndex :=
        firstEquation.symm
      _ =
          (gridPolylineSegments route).get secondIndex := by
        exact congrArg (List.get _) (Fin.ext equal)
      _ = second := secondEquation
  apply
    simple.2.2
      (first, firstIndex.val)
      (by
        rw [List.mem_zipIdx_iff_getElem?,
          List.getElem?_eq_some_iff]
        exact ⟨firstIndex.isLt, firstEquation⟩)
      (second, secondIndex.val)
      (by
        rw [List.mem_zipIdx_iff_getElem?,
          List.getElem?_eq_some_iff]
        exact ⟨secondIndex.isLt, secondEquation⟩)
      indicesDifferent

/-- Removing the first point of a simple route preserves simplicity. -/
theorem RouteIsSimple.tail
    {route : List Cell}
    (simple : RouteIsSimple route) :
    RouteIsSimple route.tail := by
  refine ⟨simple.1.tail, ?_, ?_⟩
  · intro point pointMember segment segmentMember
    apply simple.2.1 point
    · exact List.mem_of_mem_tail pointMember
    · exact
        gridPolylineSegments_tail_subset route
          segmentMember
  · intro first firstMember second secondMember
      indicesDifferent
    rw [List.mem_zipIdx_iff_getElem?,
      List.getElem?_eq_some_iff] at firstMember secondMember
    let firstIndex :
        Fin (gridPolylineSegments route.tail).length :=
      ⟨first.2, firstMember.1⟩
    let secondIndex :
        Fin (gridPolylineSegments route.tail).length :=
      ⟨second.2, secondMember.1⟩
    have tailSegmentsNodup :
        (gridPolylineSegments route.tail).Nodup :=
      gridPolylineSegments_nodup_of_points_nodup
        simple.1.tail
    have segmentsDifferent : first.1 ≠ second.1 := by
      intro equal
      have getEqual :
          (gridPolylineSegments route.tail).get firstIndex =
            (gridPolylineSegments route.tail).get secondIndex := by
        exact firstMember.2.trans
          (equal.trans secondMember.2.symm)
      have indexEqual :
          firstIndex = secondIndex :=
        (List.nodup_iff_injective_get.mp
          tailSegmentsNodup) getEqual
      apply indicesDifferent
      exact congrArg Fin.val indexEqual
    apply simple.segmentInteriorsAvoid_of_mem
    · apply gridPolylineSegments_tail_subset route
      rw [← firstMember.2]
      exact List.get_mem _ firstIndex
    · apply gridPolylineSegments_tail_subset route
      rw [← secondMember.2]
      exact List.get_mem _ secondIndex
    · exact segmentsDifferent

/-- Reversing the traversal order of a simple route preserves simplicity. -/
theorem RouteIsSimple.reverse
    {route : List Cell}
    (simple : RouteIsSimple route) :
    RouteIsSimple route.reverse := by
  refine ⟨List.nodup_reverse.mpr simple.1, ?_, ?_⟩
  · intro point pointMember segment segmentMember interior
    rw [gridPolylineSegments_reverse] at segmentMember
    rcases List.mem_map.mp segmentMember with
      ⟨original, originalMember, segmentEquation⟩
    apply simple.2.1 point
      (List.mem_reverse.mp pointMember)
      original
      (List.mem_reverse.mp originalMember)
    rw [← segmentEquation] at interior
    exact
      (GridSegment.interiorContains_reverse
        original point).mp interior
  · intro first firstMember second secondMember
      indicesDifferent
    rw [List.mem_zipIdx_iff_getElem?,
      List.getElem?_eq_some_iff] at firstMember secondMember
    let firstIndex :
        Fin (gridPolylineSegments route.reverse).length :=
      ⟨first.2, firstMember.1⟩
    let secondIndex :
        Fin (gridPolylineSegments route.reverse).length :=
      ⟨second.2, secondMember.1⟩
    have reversedSegmentsNodup :
        (gridPolylineSegments route.reverse).Nodup :=
      gridPolylineSegments_nodup_of_points_nodup
        (List.nodup_reverse.mpr simple.1)
    have segmentsDifferent : first.1 ≠ second.1 := by
      intro equal
      have getEqual :
          (gridPolylineSegments route.reverse).get firstIndex =
            (gridPolylineSegments route.reverse).get secondIndex :=
        firstMember.2.trans
          (equal.trans secondMember.2.symm)
      have indexEqual :
          firstIndex = secondIndex :=
        (List.nodup_iff_injective_get.mp
          reversedSegmentsNodup) getEqual
      apply indicesDifferent
      exact congrArg Fin.val indexEqual
    have firstPlain :
        first.1 ∈ gridPolylineSegments route.reverse := by
      rw [← firstMember.2]
      exact List.get_mem _ firstIndex
    have secondPlain :
        second.1 ∈ gridPolylineSegments route.reverse := by
      rw [← secondMember.2]
      exact List.get_mem _ secondIndex
    rw [gridPolylineSegments_reverse] at firstPlain secondPlain
    rcases List.mem_map.mp firstPlain with
      ⟨firstOriginal, firstOriginalMember, firstEquation⟩
    rcases List.mem_map.mp secondPlain with
      ⟨secondOriginal, secondOriginalMember, secondEquation⟩
    have originalsDifferent :
        firstOriginal ≠ secondOriginal := by
      intro equal
      apply segmentsDifferent
      exact firstEquation.symm.trans
        (congrArg GridSegment.reverse equal |>.trans
          secondEquation)
    have avoid :=
      simple.segmentInteriorsAvoid_of_mem
        (List.mem_reverse.mp firstOriginalMember)
        (List.mem_reverse.mp secondOriginalMember)
        originalsDifferent
    intro meet
    apply avoid
    rw [← firstEquation, ← secondEquation] at meet
    simpa using meet

end LocalIncidenceDrawing

namespace AxisDirection

/-- In a duplicate-free nonempty list, its advertised head is absent from
the tail. -/
private theorem not_mem_tail_of_nodup_of_head?_eq
    {points : List Cell} {point : Cell}
    (nodup : points.Nodup)
    (head : points.head? = some point) :
    point ∉ points.tail := by
  cases points with
  | nil =>
      simp at head
  | cons first rest =>
      have firstEqual : first = point :=
        Option.some.inj head
      simpa [firstEqual] using
        (List.nodup_cons.mp nodup).1

/-- The ordered lattice points along one genuine axis-aligned segment are
duplicate-free. -/
theorem unitSegmentPoints_nodup
    {first second : Cell}
    (aligned : (GridSegment.mk first second).IsAxisAligned) :
    (unitSegmentPoints first second).Nodup := by
  apply List.nodup_iff_injective_get.mpr
  intro firstIndex secondIndex equal
  apply Fin.ext
  have genuine :=
    between_isGenuine_of_axisAligned aligned
  simp only [unitSegmentPoints_length] at firstIndex secondIndex
  simp [unitSegmentPoints] at equal
  cases directionEquation : between first second <;>
    simp_all [IsGenuine, step, Cell.add, Cell.scale]

/-- Ordered unit subdivision preserves duplicate-freeness of every simple
orthogonal polyline. -/
theorem unitSubdividePolyline_nodup
    {points : List Cell}
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points)
    (simple :
      LocalIncidenceDrawing.RouteIsSimple points) :
    (unitSubdividePolyline points).Nodup := by
  induction points using List.twoStepInduction with
  | nil =>
      simp
  | singleton point =>
      simp
  | cons_cons first second rest _ tailInduction =>
      have orthogonalParts :=
        (List.isChain_cons_cons.mp orthogonal :
          (GridSegment.mk first second).IsAxisAligned ∧
            PeriodicOrthocrossing.OrthogonalPolyline
              (second :: rest))
      have tailSimple :
          LocalIncidenceDrawing.RouteIsSimple
            (second :: rest) := by
        simpa using simple.tail
      have tailNodup :=
        tailInduction second orthogonalParts.2 tailSimple
      have tailHead :
          (unitSubdividePolyline
            (second :: rest)).head? = some second := by
        simpa using
          unitSubdividePolyline_head?
            (points := second :: rest) (by simp)
      have secondFresh :
          second ∉
            (unitSubdividePolyline
              (second :: rest)).tail :=
        not_mem_tail_of_nodup_of_head?_eq
          tailNodup tailHead
      have firstSegmentFresh :
          GridSegment.mk first second ∉
            gridPolylineSegments (second :: rest) := by
        have segmentNodup :=
          gridPolylineSegments_nodup_of_points_nodup
            simple.1
        simpa [gridPolylineSegments] using
          (List.nodup_cons.mp segmentNodup).1
      rw [unitSubdividePolyline, joinAtEndpoint]
      apply
        (unitSegmentPoints_nodup orthogonalParts.1).append
          tailNodup.tail
      rw [List.disjoint_left]
      intro point firstMember tailMember
      have tailPointMember :
          point ∈
            unitSubdividePolyline (second :: rest) :=
        List.mem_of_mem_tail tailMember
      rcases
          unitSegmentPoints_mem_endpoint_or_interior
            orthogonalParts.1 firstMember with
        pointFirst | pointSecond | pointInterior
      · rcases
            unitSubdividePolyline_mem_original_or_segmentInterior
              orthogonalParts.2 tailPointMember with
          tailOriginal |
          ⟨tailSegment, tailSegmentMember, tailInterior⟩
        · subst point
          exact (List.nodup_cons.mp simple.1).1 tailOriginal
        · subst point
          apply
            simple.2.1 first
              (by simp)
              tailSegment
              (gridPolylineSegments_tail_subset
                (first :: second :: rest)
                tailSegmentMember)
          exact tailInterior
      · subst point
        exact secondFresh tailMember
      · rcases
            unitSubdividePolyline_mem_original_or_segmentInterior
              orthogonalParts.2 tailPointMember with
          tailOriginal |
          ⟨tailSegment, tailSegmentMember, tailInterior⟩
        · apply
            simple.2.1 point
              (List.mem_cons_of_mem first tailOriginal)
              (GridSegment.mk first second)
              (by simp [gridPolylineSegments])
          exact pointInterior
        · have interiorsAvoid :=
            simple.segmentInteriorsAvoid_of_mem
              (first :=
                GridSegment.mk first second)
              (second := tailSegment)
              (by simp [gridPolylineSegments])
              (gridPolylineSegments_tail_subset
                (first :: second :: rest)
                tailSegmentMember)
              (fun equal =>
                firstSegmentFresh
                  (by simpa [equal] using tailSegmentMember))
          apply interiorsAvoid
          exact
            GridSegment.interiorsMeet_of_interiorContains
              pointInterior tailInterior

end AxisDirection
end LeanTrominoes
