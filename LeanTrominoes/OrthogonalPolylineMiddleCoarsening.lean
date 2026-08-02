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

set_option maxRecDepth 4096

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
    StrictlyBetween] at middleInterior pointInterior ⊢
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

/-- Each open subsegment obtained by splitting at an interior point is
contained in the open original segment. -/
theorem interiorContains_of_split
    {first middle finish point : Cell}
    (middleInterior :
      (GridSegment.mk first finish).InteriorContains middle)
    (pointInterior :
      (GridSegment.mk first middle).InteriorContains point ∨
        (GridSegment.mk middle finish).InteriorContains point) :
    (GridSegment.mk first finish).InteriorContains point := by
  rcases first with ⟨firstX, firstY⟩
  rcases middle with ⟨middleX, middleY⟩
  rcases finish with ⟨finishX, finishY⟩
  rcases point with ⟨pointX, pointY⟩
  simp only [InteriorContains, IsHorizontal, IsVertical,
    StrictlyBetween] at middleInterior pointInterior ⊢
  rcases middleInterior with
      ⟨longHorizontal, middleYEq, middleBetween⟩ |
      ⟨longVertical, middleXEq, middleBetween⟩
  · rcases pointInterior with
        (⟨splitHorizontal, pointYEq, pointBetween⟩ |
          ⟨splitVertical, pointXEq, pointBetween⟩) |
        (⟨splitHorizontal, pointYEq, pointBetween⟩ |
          ⟨splitVertical, pointXEq, pointBetween⟩)
    · exact Or.inl
        ⟨longHorizontal, pointYEq, by omega⟩
    · exfalso
      omega
    · exact Or.inl
        ⟨longHorizontal, by omega, by omega⟩
    · exfalso
      omega
  · rcases pointInterior with
        (⟨splitHorizontal, pointYEq, pointBetween⟩ |
          ⟨splitVertical, pointXEq, pointBetween⟩) |
        (⟨splitHorizontal, pointYEq, pointBetween⟩ |
          ⟨splitVertical, pointXEq, pointBetween⟩)
    · exfalso
      omega
    · exact Or.inr
        ⟨longVertical, pointXEq, by omega⟩
    · exfalso
      omega
    · exact Or.inr
        ⟨longVertical, by omega, by omega⟩

/-- Strict betweenness in the first half of a split interval implies
strict betweenness in the original interval. -/
theorem StrictlyBetween.of_split_left
    {first middle finish point : Int}
    (middleBetween : StrictlyBetween first finish middle)
    (pointBetween : StrictlyBetween first middle point) :
    StrictlyBetween first finish point := by
  unfold StrictlyBetween at middleBetween pointBetween ⊢
  omega

/-- Strict betweenness in the second half of a split interval implies
strict betweenness in the original interval. -/
theorem StrictlyBetween.of_split_right
    {first middle finish point : Int}
    (middleBetween : StrictlyBetween first finish middle)
    (pointBetween : StrictlyBetween middle finish point) :
    StrictlyBetween first finish point := by
  unfold StrictlyBetween at middleBetween pointBetween ⊢
  omega

/-- Overlap with the first half of a split open interval implies overlap
with the original open interval. -/
theorem OpenIntervalsOverlap.of_split_left
    {first middle finish otherStart otherFinish : Int}
    (middleBetween : StrictlyBetween first finish middle)
    (overlap :
      OpenIntervalsOverlap first middle otherStart otherFinish) :
    OpenIntervalsOverlap first finish otherStart otherFinish := by
  unfold StrictlyBetween at middleBetween
  unfold OpenIntervalsOverlap at overlap ⊢
  simp only [min_lt_iff, lt_max_iff] at overlap ⊢
  omega

/-- Overlap with the second half of a split open interval implies overlap
with the original open interval. -/
theorem OpenIntervalsOverlap.of_split_right
    {first middle finish otherStart otherFinish : Int}
    (middleBetween : StrictlyBetween first finish middle)
    (overlap :
      OpenIntervalsOverlap middle finish otherStart otherFinish) :
    OpenIntervalsOverlap first finish otherStart otherFinish := by
  unfold StrictlyBetween at middleBetween
  unfold OpenIntervalsOverlap at overlap ⊢
  simp only [min_lt_iff, lt_max_iff] at overlap ⊢
  omega

/-- An interior intersection with either open subsegment is also an
interior intersection with the original segment. -/
theorem interiorsMeet_of_split_left
    {first middle finish : Cell}
    {other : GridSegment}
    (middleInterior :
      (GridSegment.mk first finish).InteriorContains middle)
    (meet :
      (GridSegment.mk first middle).InteriorsMeet other ∨
        (GridSegment.mk middle finish).InteriorsMeet other) :
    (GridSegment.mk first finish).InteriorsMeet other := by
  unfold InteriorContains at middleInterior
  unfold InteriorsMeet at meet ⊢
  rcases middleInterior with
      ⟨longHorizontal, middleYEq, middleBetween⟩ |
      ⟨longVertical, middleXEq, middleBetween⟩
  · rcases meet with
        (horizontal | vertical | horizontalVertical |
          verticalHorizontal) |
        (horizontal | vertical | horizontalVertical |
          verticalHorizontal)
    · exact Or.inl
        ⟨longHorizontal, horizontal.2.1,
          horizontal.2.2.1,
          OpenIntervalsOverlap.of_split_left
            middleBetween horizontal.2.2.2⟩
    · exfalso
      exact vertical.1.2 middleYEq.symm
    · exact Or.inr <| Or.inr <| Or.inl
        ⟨longHorizontal, horizontalVertical.2.1,
          StrictlyBetween.of_split_left
            middleBetween horizontalVertical.2.2.1,
          horizontalVertical.2.2.2⟩
    · exfalso
      exact verticalHorizontal.1.2
        middleYEq.symm
    · exact Or.inl
        ⟨longHorizontal, horizontal.2.1,
          middleYEq.symm.trans horizontal.2.2.1,
          OpenIntervalsOverlap.of_split_right
            middleBetween horizontal.2.2.2⟩
    · exfalso
      exact vertical.1.2 (middleYEq.trans longHorizontal.1)
    · exact Or.inr <| Or.inr <| Or.inl
        ⟨longHorizontal, horizontalVertical.2.1,
          StrictlyBetween.of_split_right middleBetween
            horizontalVertical.2.2.1,
          by simpa [middleYEq] using
            horizontalVertical.2.2.2⟩
    · exfalso
      exact verticalHorizontal.1.2
        (middleYEq.trans longHorizontal.1)
  · rcases meet with
        (horizontal | vertical | horizontalVertical |
          verticalHorizontal) |
        (horizontal | vertical | horizontalVertical |
          verticalHorizontal)
    · exfalso
      exact horizontal.1.2 middleXEq.symm
    · exact Or.inr <| Or.inl
        ⟨longVertical, vertical.2.1,
          vertical.2.2.1,
          OpenIntervalsOverlap.of_split_left
            middleBetween vertical.2.2.2⟩
    · exfalso
      exact horizontalVertical.1.2
        middleXEq.symm
    · exact Or.inr <| Or.inr <| Or.inr
        ⟨longVertical, verticalHorizontal.2.1,
          verticalHorizontal.2.2.1,
          StrictlyBetween.of_split_left middleBetween
            verticalHorizontal.2.2.2⟩
    · exfalso
      exact horizontal.1.2 (middleXEq.trans longVertical.1)
    · exact Or.inr <| Or.inl
        ⟨longVertical, vertical.2.1,
          middleXEq.symm.trans vertical.2.2.1,
          OpenIntervalsOverlap.of_split_right
            middleBetween vertical.2.2.2⟩
    · exfalso
      exact horizontalVertical.1.2
        (middleXEq.trans longVertical.1)
    · exact Or.inr <| Or.inr <| Or.inr
        ⟨longVertical, verticalHorizontal.2.1,
          by simpa [middleXEq] using
            verticalHorizontal.2.2.1,
          StrictlyBetween.of_split_right middleBetween
            verticalHorizontal.2.2.2⟩

/-- Two open intervals containing the same point overlap. -/
theorem OpenIntervalsOverlap.of_common_strictlyBetween
    {firstStart firstFinish secondStart secondFinish point : Int}
    (firstContains :
      StrictlyBetween firstStart firstFinish point)
    (secondContains :
      StrictlyBetween secondStart secondFinish point) :
    OpenIntervalsOverlap
      firstStart firstFinish secondStart secondFinish := by
  unfold StrictlyBetween at firstContains secondContains
  unfold OpenIntervalsOverlap
  simp only [min_lt_iff, lt_max_iff]
  omega

/-- If the split point is interior to another segment, then that segment
meets the original segment in their relative interiors. -/
theorem interiorsMeet_of_interiorContains_split_point
    {first middle finish : Cell}
    {other : GridSegment}
    (middleInterior :
      (GridSegment.mk first finish).InteriorContains middle)
    (otherInterior : other.InteriorContains middle) :
    (GridSegment.mk first finish).InteriorsMeet other := by
  unfold InteriorContains at middleInterior otherInterior
  unfold InteriorsMeet
  rcases middleInterior with
      ⟨longHorizontal, middleYEq, middleBetween⟩ |
      ⟨longVertical, middleXEq, middleBetween⟩
  · rcases otherInterior with
      ⟨otherHorizontal, otherYEq, otherBetween⟩ |
      ⟨otherVertical, otherXEq, otherBetween⟩
    · exact Or.inl
        ⟨longHorizontal, otherHorizontal,
          middleYEq.symm.trans otherYEq,
          OpenIntervalsOverlap.of_common_strictlyBetween
            middleBetween otherBetween⟩
    · exact Or.inr <| Or.inr <| Or.inl
        ⟨longHorizontal, otherVertical,
          by simpa [otherXEq] using middleBetween,
          by simpa [middleYEq] using otherBetween⟩
  · rcases otherInterior with
      ⟨otherHorizontal, otherYEq, otherBetween⟩ |
      ⟨otherVertical, otherXEq, otherBetween⟩
    · exact Or.inr <| Or.inr <| Or.inr
        ⟨longVertical, otherHorizontal,
          by simpa [middleXEq] using otherBetween,
          by simpa [otherYEq] using middleBetween⟩
    · exact Or.inr <| Or.inl
        ⟨longVertical, otherVertical,
          middleXEq.symm.trans otherXEq,
          OpenIntervalsOverlap.of_common_strictlyBetween
            middleBetween otherBetween⟩

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

/-- Inserting an interior subdivision point into a segment on the left
preserves strict continuous separation. -/
theorem RoutesStrictlyAvoidEachOther.refine_middle_left
    {first middle finish : Cell}
    {other : List Cell}
    (strict :
      RoutesStrictlyAvoidEachOther [first, finish] other)
    (middleInterior :
      (GridSegment.mk first finish).InteriorContains middle) :
    RoutesStrictlyAvoidEachOther
      [first, middle, finish] other := by
  unfold RoutesStrictlyAvoidEachOther at strict ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro split splitMember otherSegment otherMember meet
    simp [gridPolylineSegments] at splitMember
    rcases splitMember with rfl | rfl
    · exact strict.1
        (GridSegment.mk first finish)
        (by simp [gridPolylineSegments])
        otherSegment otherMember
        (GridSegment.interiorsMeet_of_split_left
          middleInterior (Or.inl meet))
    · exact strict.1
        (GridSegment.mk first finish)
        (by simp [gridPolylineSegments])
        otherSegment otherMember
        (GridSegment.interiorsMeet_of_split_left
          middleInterior (Or.inr meet))
  · intro splitPoint splitMember otherSegment otherMember
    simp only [List.mem_cons, List.not_mem_nil, or_false]
      at splitMember
    rcases splitMember with pointEq | pointEq | pointEq
    · subst splitPoint
      exact strict.2.1 first (by simp)
        otherSegment otherMember
    · subst splitPoint
      intro otherInterior
      exact strict.1
        (GridSegment.mk first finish)
        (by simp [gridPolylineSegments])
        otherSegment otherMember
        (GridSegment.interiorsMeet_of_interiorContains_split_point
          middleInterior otherInterior)
    · subst splitPoint
      exact strict.2.1 finish (by simp)
        otherSegment otherMember
  · intro otherPoint otherMember split splitMember pointInterior
    simp [gridPolylineSegments] at splitMember
    rcases splitMember with rfl | rfl
    · exact strict.2.2.1 otherPoint otherMember
        (GridSegment.mk first finish)
        (by simp [gridPolylineSegments])
        (GridSegment.interiorContains_of_split
          middleInterior (Or.inl pointInterior))
    · exact strict.2.2.1 otherPoint otherMember
        (GridSegment.mk first finish)
        (by simp [gridPolylineSegments])
        (GridSegment.interiorContains_of_split
          middleInterior (Or.inr pointInterior))
  · intro splitPoint splitMember otherPoint otherMember pointsEqual
    simp only [List.mem_cons, List.not_mem_nil, or_false]
      at splitMember
    rcases splitMember with pointEq | pointEq | pointEq
    · exact strict.2.2.2 first (by simp)
        otherPoint otherMember (pointEq.symm.trans pointsEqual)
    · have middleEqOther :
          middle = otherPoint :=
        pointEq.symm.trans pointsEqual
      apply strict.2.2.1 otherPoint otherMember
        (GridSegment.mk first finish)
        (by simp [gridPolylineSegments])
      simpa [middleEqOther] using middleInterior
    ·
      exact strict.2.2.2 finish (by simp)
        otherPoint otherMember (pointEq.symm.trans pointsEqual)

/-- Symmetric right-route form of middle-point refinement. -/
theorem RoutesStrictlyAvoidEachOther.refine_middle_right
    {other : List Cell}
    {first middle finish : Cell}
    (strict :
      RoutesStrictlyAvoidEachOther other [first, finish])
    (middleInterior :
      (GridSegment.mk first finish).InteriorContains middle) :
    RoutesStrictlyAvoidEachOther
      other [first, middle, finish] :=
  (strict.symm.refine_middle_left middleInterior).symm

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
