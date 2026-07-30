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

end PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

end LeanTrominoes
