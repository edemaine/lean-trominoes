import LeanTrominoes.OrthogonalPolylineStrictSeparation

/-!
# Removing a collinear subdivision point

Inserting an interior point into one axis-aligned segment does not change
the geometric trace of a route.  This file proves the converse operation
needed by the retained angular fan: strict continuous separation of the
subdivided two-segment route implies strict separation after the middle
point is removed.
-/

namespace LeanTrominoes

/-- Joining three routes is associative when the middle route is nonempty. -/
theorem joinAtEndpoint_assoc_of_middle_ne_nil
    {first middle last : List Cell}
    (middleNe : middle ≠ []) :
    joinAtEndpoint first
        (joinAtEndpoint middle last) =
      joinAtEndpoint
        (joinAtEndpoint first middle) last := by
  unfold joinAtEndpoint
  rw [List.tail_append_of_ne_nil middleNe]
  exact (List.append_assoc _ _ _).symm

/-- The points of a correctly joined route are exactly the points of its
two constituent routes. -/
theorem mem_joinAtEndpoint_iff
    {first second : List Cell}
    {boundary point : Cell}
    (firstLast : first.getLast? = some boundary)
    (secondHead : second.head? = some boundary) :
    point ∈ joinAtEndpoint first second ↔
      point ∈ first ∨ point ∈ second := by
  constructor
  · exact mem_joinAtEndpoint
  · intro member
    rw [joinAtEndpoint, List.mem_append]
    rcases member with firstMember | secondMember
    · exact Or.inl firstMember
    · cases second with
      | nil =>
          simp at secondHead
      | cons head tail =>
          simp only [List.head?_cons, Option.some.injEq] at secondHead
          subst head
          simp only [List.mem_cons] at secondMember
          rcases secondMember with rfl | tailMember
          · exact Or.inl (mem_of_getLast?_eq_some firstLast)
          · exact Or.inr tailMember

namespace GridSegment

/-- A point in the interior of a segment split at another interior point is
the split point itself or lies in one of the two resulting interiors. -/
theorem interiorContains_split
    {first middle finish point : Cell}
    (middleInterior :
      (GridSegment.mk first finish).InteriorContains middle)
    (pointInterior :
      (GridSegment.mk first finish).InteriorContains point) :
    point = middle ∨
      (GridSegment.mk first middle).InteriorContains point ∨
      (GridSegment.mk middle finish).InteriorContains point := by
  rcases first with ⟨firstX, firstY⟩
  rcases middle with ⟨middleX, middleY⟩
  rcases finish with ⟨finishX, finishY⟩
  rcases point with ⟨pointX, pointY⟩
  simp only [InteriorContains, IsHorizontal, IsVertical,
    StrictlyBetween, Prod.mk.injEq] at middleInterior pointInterior ⊢
  rcases middleInterior with horizontal | vertical <;>
    rcases pointInterior with pointHorizontal | pointVertical <;>
    simp_all <;>
    omega

/-- If the unsplit segment meets another segment in their relative
interiors, then one split segment meets it or the other segment contains the
split point in its relative interior. -/
theorem interiorsMeet_split_left
    {first middle finish : Cell}
    {other : GridSegment}
    (middleInterior :
      (GridSegment.mk first finish).InteriorContains middle)
    (meet :
      (GridSegment.mk first finish).InteriorsMeet other) :
    (GridSegment.mk first middle).InteriorsMeet other ∨
      (GridSegment.mk middle finish).InteriorsMeet other ∨
      other.InteriorContains middle := by
  by_contra none
  push Not at none
  rcases other with ⟨⟨otherStartX, otherStartY⟩,
    ⟨otherFinishX, otherFinishY⟩⟩
  rcases first with ⟨firstX, firstY⟩
  rcases middle with ⟨middleX, middleY⟩
  rcases finish with ⟨finishX, finishY⟩
  simp only [InteriorsMeet, InteriorContains,
    IsHorizontal, IsVertical, OpenIntervalsOverlap,
    StrictlyBetween, min_lt_iff, lt_max_iff]
    at middleInterior meet none
  rcases middleInterior with horizontal | vertical <;>
    rcases meet with meet | meet | meet | meet <;>
    simp_all <;>
    omega

end GridSegment

namespace PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

open GridSegment

/-- Removing the middle point from a split segment on the left preserves
strict continuous separation. -/
theorem RoutesStrictlyAvoidEachOther.coarsen_middle_left
    {first middle finish : Cell}
    {other : List Cell}
    (strict :
      RoutesStrictlyAvoidEachOther
        [first, middle, finish] other)
    (middleInterior :
      (GridSegment.mk first finish).InteriorContains middle) :
    RoutesStrictlyAvoidEachOther [first, finish] other := by
  unfold RoutesStrictlyAvoidEachOther at strict ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro long longMember otherSegment otherMember meet
    simp [gridPolylineSegments] at longMember
    subst long
    rcases GridSegment.interiorsMeet_split_left
        middleInterior meet with
      firstMeet | secondMeet | middleContains
    · exact strict.1
        (GridSegment.mk first middle)
        (by simp [gridPolylineSegments])
        otherSegment otherMember firstMeet
    · exact strict.1
        (GridSegment.mk middle finish)
        (by simp [gridPolylineSegments])
        otherSegment otherMember secondMeet
    · exact strict.2.1 middle (by simp)
        otherSegment otherMember middleContains
  · intro firstPoint firstMember otherSegment otherMember
    have firstMember' :
        firstPoint ∈ [first, middle, finish] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
        at firstMember ⊢
      rcases firstMember with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr rfl)
    exact strict.2.1 firstPoint firstMember'
      otherSegment otherMember
  · intro otherPoint otherMember long longMember pointInterior
    simp [gridPolylineSegments] at longMember
    subst long
    rcases GridSegment.interiorContains_split
        middleInterior pointInterior with
      pointEq | firstInterior | secondInterior
    · exact
        (strict.2.2.2 middle (by simp)
          otherPoint otherMember) pointEq.symm
    · exact strict.2.2.1 otherPoint otherMember
        (GridSegment.mk first middle)
        (by simp [gridPolylineSegments])
        firstInterior
    · exact strict.2.2.1 otherPoint otherMember
        (GridSegment.mk middle finish)
        (by simp [gridPolylineSegments])
        secondInterior
  · intro firstPoint firstMember otherPoint otherMember
    have firstMember' :
        firstPoint ∈ [first, middle, finish] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
        at firstMember ⊢
      rcases firstMember with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr rfl)
    exact strict.2.2.2 firstPoint firstMember'
      otherPoint otherMember

/-- Symmetric right-route form of middle-point coarsening. -/
theorem RoutesStrictlyAvoidEachOther.coarsen_middle_right
    {other : List Cell}
    {first middle finish : Cell}
    (strict :
      RoutesStrictlyAvoidEachOther
        other [first, middle, finish])
    (middleInterior :
      (GridSegment.mk first finish).InteriorContains middle) :
    RoutesStrictlyAvoidEachOther other [first, finish] :=
  (strict.symm.coarsen_middle_left middleInterior).symm

/-- Strict separation of a joined route implies strict separation of each
of its two constituent routes. -/
theorem RoutesStrictlyAvoidEachOther.of_join_left
    {first extra other : List Cell}
    {boundary : Cell}
    (strict :
      RoutesStrictlyAvoidEachOther
        (joinAtEndpoint first extra) other)
    (firstLast : first.getLast? = some boundary)
    (extraHead : extra.head? = some boundary) :
    RoutesStrictlyAvoidEachOther first other ∧
      RoutesStrictlyAvoidEachOther extra other := by
  have segments :=
    gridPolylineSegments_joinAtEndpoint firstLast extraHead
  have points (point : Cell) :
      point ∈ joinAtEndpoint first extra ↔
        point ∈ first ∨ point ∈ extra :=
    mem_joinAtEndpoint_iff firstLast extraHead
  unfold RoutesStrictlyAvoidEachOther at strict ⊢
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro firstSegment firstMember otherSegment otherMember
      have joinedMember :
          firstSegment ∈
            gridPolylineSegments
              (joinAtEndpoint first extra) := by
        rw [segments, List.mem_append]
        exact Or.inl firstMember
      exact strict.1 firstSegment joinedMember
        otherSegment otherMember
    · intro firstPoint firstMember otherSegment otherMember
      exact strict.2.1 firstPoint
        (points firstPoint |>.mpr (Or.inl firstMember))
        otherSegment otherMember
    · intro otherPoint otherMember firstSegment firstMember
      apply strict.2.2.1 otherPoint otherMember firstSegment
      rw [segments, List.mem_append]
      exact Or.inl firstMember
    · intro firstPoint firstMember otherPoint otherMember
      exact strict.2.2.2 firstPoint
        (points firstPoint |>.mpr (Or.inl firstMember))
        otherPoint otherMember
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro extraSegment extraMember otherSegment otherMember
      have joinedMember :
          extraSegment ∈
            gridPolylineSegments
              (joinAtEndpoint first extra) := by
        rw [segments, List.mem_append]
        exact Or.inr extraMember
      exact strict.1 extraSegment joinedMember
        otherSegment otherMember
    · intro extraPoint extraMember otherSegment otherMember
      exact strict.2.1 extraPoint
        (points extraPoint |>.mpr (Or.inr extraMember))
        otherSegment otherMember
    · intro otherPoint otherMember extraSegment extraMember
      apply strict.2.2.1 otherPoint otherMember extraSegment
      rw [segments, List.mem_append]
      exact Or.inr extraMember
    · intro extraPoint extraMember otherPoint otherMember
      exact strict.2.2.2 extraPoint
        (points extraPoint |>.mpr (Or.inr extraMember))
        otherPoint otherMember

/-- Symmetric right-route form of extracting the two parts of a join. -/
theorem RoutesStrictlyAvoidEachOther.of_join_right
    {other first extra : List Cell}
    {boundary : Cell}
    (strict :
      RoutesStrictlyAvoidEachOther
        other (joinAtEndpoint first extra))
    (firstLast : first.getLast? = some boundary)
    (extraHead : extra.head? = some boundary) :
    RoutesStrictlyAvoidEachOther other first ∧
      RoutesStrictlyAvoidEachOther other extra := by
  have parts := strict.symm.of_join_left firstLast extraHead
  exact ⟨parts.1.symm, parts.2.symm⟩

/-- Coarsen the trailing three-point part of a joined left route. -/
theorem RoutesStrictlyAvoidEachOther.coarsen_middle_after_join_left
    {leading other : List Cell}
    {first middle finish : Cell}
    (strict :
      RoutesStrictlyAvoidEachOther
        (joinAtEndpoint leading [first, middle, finish])
        other)
    (leadingLast : leading.getLast? = some first)
    (middleInterior :
      (GridSegment.mk first finish).InteriorContains middle) :
    RoutesStrictlyAvoidEachOther
      (joinAtEndpoint leading [first, finish]) other := by
  have parts :=
    strict.of_join_left leadingLast (by simp)
  exact parts.1.join_left
    (parts.2.coarsen_middle_left middleInterior)
    leadingLast (by simp)

/-- Symmetric right-route form of coarsening a trailing joined segment. -/
theorem RoutesStrictlyAvoidEachOther.coarsen_middle_after_join_right
    {other leading : List Cell}
    {first middle finish : Cell}
    (strict :
      RoutesStrictlyAvoidEachOther
        other (joinAtEndpoint leading [first, middle, finish]))
    (leadingLast : leading.getLast? = some first)
    (middleInterior :
      (GridSegment.mk first finish).InteriorContains middle) :
    RoutesStrictlyAvoidEachOther
      other (joinAtEndpoint leading [first, finish]) :=
  (strict.symm.coarsen_middle_after_join_left
    leadingLast middleInterior).symm

end PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

end LeanTrominoes
