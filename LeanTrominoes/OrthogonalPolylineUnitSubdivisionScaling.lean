import LeanTrominoes.OrthogonalPolylineScaling
import LeanTrominoes.OrthogonalPolylineUnitSubdivisionJoin
import LeanTrominoes.OrthogonalPolylineUnitSubdivisionTranslation
import LeanTrominoes.RetainedTerminalCheckpointRasterization

/-!
# Endpoint isolation through positive polyline scaling

Positive integral scaling inserts extra lattice points along every source
segment.  It cannot, however, create a new visit to a scaled source lattice
point: any such visit reflects to the corresponding point of the original
unit subdivision.  This file packages that reflection and uses it to
transport isolation of both route endpoints through scaling and translation.
-/

namespace LeanTrominoes
namespace AxisDirection

/-- If a scaled source lattice point occurs in the unit subdivision of a
scaled orthogonal route, then its unscaled point occurs in the original unit
subdivision. -/
theorem mem_unitSubdividePolyline_scale_reflect
    {points : List Cell} {point : Cell} {factor : Nat}
    (factorPositive : 0 < factor)
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points)
    (member :
      Cell.scale (factor : Int) point ∈
        unitSubdividePolyline (scalePolyline (factor : Int) points)) :
    point ∈ unitSubdividePolyline points := by
  have scaledOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline
        (scalePolyline (factor : Int) points) :=
    orthogonal.scalePolyline factorPositive
  rcases
      unitSubdividePolyline_mem_original_or_segmentInterior
        scaledOrthogonal member with
    originalMember | ⟨scaledSegment, scaledSegmentMember,
      scaledInterior⟩
  · rcases List.mem_map.mp originalMember with
      ⟨originalPoint, originalPointMember, pointEquation⟩
    have originalPointEqual : originalPoint = point := by
      apply Cell.scale_injective (factor := (factor : Int))
        (by exact_mod_cast Nat.ne_of_gt factorPositive)
      exact pointEquation.trans rfl
    subst originalPoint
    exact mem_unitSubdividePolyline_of_mem
      orthogonal originalPointMember
  · rw [gridPolylineSegments_scalePolyline] at scaledSegmentMember
    rcases List.mem_map.mp scaledSegmentMember with
      ⟨originalSegment, originalSegmentMember, segmentEquation⟩
    have originalInterior :
        originalSegment.InteriorContains point := by
      rw [← GridSegment.interiorContains_scale_iff
        (factor := (factor : Int))
        (by exact_mod_cast factorPositive)]
      simpa [← segmentEquation] using scaledInterior
    exact mem_unitSubdividePolyline_of_segment_contains
      orthogonal originalSegmentMember
      (GridSegment.contains_of_interiorContains originalInterior)

/-- Positive integral scaling preserves isolation of the first endpoint
after unit subdivision. -/
theorem HeadNotInTail.unitSubdividePolyline_scalePolyline
    {points : List Cell} {factor : Nat}
    (fresh : HeadNotInTail (unitSubdividePolyline points))
    (factorPositive : 0 < factor)
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points) :
    HeadNotInTail
      (unitSubdividePolyline
        (scalePolyline (factor : Int) points)) := by
  induction points using List.twoStepInduction with
  | nil => simp [HeadNotInTail]
  | singleton point => simp [HeadNotInTail]
  | cons_cons first second rest _tailInduction =>
      have orthogonalParts :=
        (List.isChain_cons_cons.mp orthogonal :
          (GridSegment.mk first second).IsAxisAligned ∧
            PeriodicOrthocrossing.OrthogonalPolyline
              (second :: rest))
      have scaledAligned :
          (GridSegment.mk
            (Cell.scale (factor : Int) first)
            (Cell.scale (factor : Int) second)).IsAxisAligned := by
        exact
          (GridSegment.isAxisAligned_scale_iff
            (by exact_mod_cast factorPositive)
            (GridSegment.mk first second)).mpr orthogonalParts.1
      intro scaledHead scaledHeadLookup scaledHeadMember
      have scaledHeadEqual :
          scaledHead = Cell.scale (factor : Int) first := by
        symm
        simpa [scalePolyline, unitSubdividePolyline,
          LeanTrominoes.joinAtEndpoint] using scaledHeadLookup
      subst scaledHead
      have sourceHeadLookup :
          (unitSubdividePolyline
            (first :: second :: rest)).head? = some first := by
        simpa using
          unitSubdividePolyline_head?
            (points := first :: second :: rest) (by simp)
      have sourceAbsent := fresh first sourceHeadLookup
      have scaledFirstSegmentFresh :
          HeadNotInTail
            (unitSegmentPoints
              (Cell.scale (factor : Int) first)
              (Cell.scale (factor : Int) second)) :=
        headNotInTail_of_nodup
          (unitSegmentPoints_nodup scaledAligned)
      have scaledFirstSegmentNonempty :
          unitSegmentPoints
              (Cell.scale (factor : Int) first)
              (Cell.scale (factor : Int) second) ≠ [] := by
        intro empty
        have headLookup :=
          unitSegmentPoints_head?
            (Cell.scale (factor : Int) first)
            (Cell.scale (factor : Int) second)
        rw [empty] at headLookup
        simp at headLookup
      change
        Cell.scale (factor : Int) first ∈
          (unitSubdividePolyline
            (Cell.scale (factor : Int) first ::
              Cell.scale (factor : Int) second ::
              scalePolyline (factor : Int) rest)).tail
          at scaledHeadMember
      rw [unitSubdividePolyline,
        LeanTrominoes.joinAtEndpoint] at scaledHeadMember
      simp only [List.tail_append_of_ne_nil scaledFirstSegmentNonempty,
        List.mem_append] at scaledHeadMember
      rcases scaledHeadMember with
        firstSegmentMember | transformedTailMember
      · exact
          scaledFirstSegmentFresh
            (Cell.scale (factor : Int) first)
            (unitSegmentPoints_head?
              (Cell.scale (factor : Int) first)
              (Cell.scale (factor : Int) second))
            firstSegmentMember
      · have transformedTailFullMember :
            Cell.scale (factor : Int) first ∈
              unitSubdividePolyline
                (scalePolyline (factor : Int) (second :: rest)) :=
          List.mem_of_mem_tail transformedTailMember
        have sourceTailMember :
            first ∈
              unitSubdividePolyline (second :: rest) :=
          mem_unitSubdividePolyline_scale_reflect
            factorPositive orthogonalParts.2
            transformedTailFullMember
        apply sourceAbsent
        rw [unitSubdividePolyline,
          LeanTrominoes.joinAtEndpoint]
        have firstSegmentNonempty :
            unitSegmentPoints first second ≠ [] := by
          intro empty
          have headLookup := unitSegmentPoints_head? first second
          rw [empty] at headLookup
          simp at headLookup
        simp only [List.tail_append_of_ne_nil firstSegmentNonempty,
          List.mem_append]
        right
        have firstNeSecond : first ≠ second := by
          intro equal
          subst second
          simpa [GridSegment.IsAxisAligned,
            GridSegment.IsHorizontal,
            GridSegment.IsVertical] using orthogonalParts.1
        have tailHead :
            (unitSubdividePolyline
              (second :: rest)).head? = some second := by
          simpa using
            unitSubdividePolyline_head?
              (points := second :: rest) (by simp)
        cases subdividedTailEquation :
            unitSubdividePolyline (second :: rest) with
        | nil => simp [subdividedTailEquation] at tailHead
        | cons actualHead actualTail =>
            have actualHeadEqual : actualHead = second := by
              simpa [subdividedTailEquation] using tailHead
            subst actualHead
            simp only [subdividedTailEquation,
              List.mem_cons] at sourceTailMember
            exact sourceTailMember.resolve_left firstNeSecond

/-- Positive integral scaling preserves isolation of the final endpoint
after unit subdivision. -/
theorem LastNotInDropLast.unitSubdividePolyline_scalePolyline
    {points : List Cell} {factor : Nat}
    (fresh : LastNotInDropLast (unitSubdividePolyline points))
    (factorPositive : 0 < factor)
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points) :
    LastNotInDropLast
      (unitSubdividePolyline
        (scalePolyline (factor : Int) points)) := by
  induction points using List.twoStepInduction with
  | nil => simp [LastNotInDropLast]
  | singleton point => simp [LastNotInDropLast]
  | cons_cons first second rest _ tailInduction =>
      have orthogonalParts :=
        (List.isChain_cons_cons.mp orthogonal :
          (GridSegment.mk first second).IsAxisAligned ∧
            PeriodicOrthocrossing.OrthogonalPolyline
              (second :: rest))
      have scaledAligned :
          (GridSegment.mk
            (Cell.scale (factor : Int) first)
            (Cell.scale (factor : Int) second)).IsAxisAligned := by
        exact
          (GridSegment.isAxisAligned_scale_iff
            (by exact_mod_cast factorPositive)
            (GridSegment.mk first second)).mpr orthogonalParts.1
      cases rest with
      | nil =>
          have segmentFresh :
              LastNotInDropLast
                (unitSegmentPoints
                  (Cell.scale (factor : Int) first)
                  (Cell.scale (factor : Int) second)) :=
            lastNotInDropLast_of_nodup
              (unitSegmentPoints_nodup scaledAligned)
          simpa [scalePolyline, unitSubdividePolyline,
            LeanTrominoes.joinAtEndpoint] using segmentFresh
      | cons third tail =>
          let sourceFirst : List Cell := [first, second]
          let sourceSecond : List Cell := second :: third :: tail
          have sourceFirstLast :
              sourceFirst.getLast? = some second := by
            simp [sourceFirst]
          have sourceSecondHead :
              sourceSecond.head? = some second := by
            simp [sourceSecond]
          have sourceSplit :=
            LeanTrominoes.AxisDirection.unitSubdividePolyline_joinAtEndpoint
              (first := sourceFirst) (second := sourceSecond)
              (firstNonempty := by simp [sourceFirst])
              (firstLast := sourceFirstLast)
              (secondHead := sourceSecondHead)
          have sourceFreshJoined :
              LastNotInDropLast
                (LeanTrominoes.joinAtEndpoint
                  (unitSubdividePolyline sourceFirst)
                  (unitSubdividePolyline sourceSecond)) := by
            rw [← sourceSplit]
            simpa [sourceFirst, sourceSecond,
              LeanTrominoes.joinAtEndpoint] using fresh
          have sourceFirstOrthogonal :
              PeriodicOrthocrossing.OrthogonalPolyline sourceFirst := by
            simpa [sourceFirst,
              PeriodicOrthocrossing.OrthogonalPolyline] using
              orthogonalParts.1
          have sourceFirstSubdividedLast :
              (unitSubdividePolyline sourceFirst).getLast? =
                some second := by
            rw [unitSubdividePolyline_getLast?
              (by simp [sourceFirst]) sourceFirstOrthogonal,
              sourceFirstLast]
          have sourceSecondSubdividedHead :
              (unitSubdividePolyline sourceSecond).head? =
                some second := by
            rw [unitSubdividePolyline_head?
              (by simp [sourceSecond]), sourceSecondHead]
          have sourceSecondSubdividedLength :
              2 ≤ (unitSubdividePolyline sourceSecond).length :=
            unitSubdividePolyline_length_ge_two_of_length_ge_two
              (by simp [sourceSecond]) orthogonalParts.2
          have sourceSecondFresh :
              LastNotInDropLast
                (unitSubdividePolyline sourceSecond) :=
            sourceFreshJoined.of_joinAtEndpoint_right
              sourceFirstSubdividedLast
              sourceSecondSubdividedHead
              sourceSecondSubdividedLength
          let sourceLast := sourceSecond.getLast (by simp [sourceSecond])
          have sourceSecondLast :
              sourceSecond.getLast? = some sourceLast :=
            List.getLast?_eq_some_getLast (by simp [sourceSecond])
          have sourceSecondSubdividedLast :
              (unitSubdividePolyline sourceSecond).getLast? =
                some sourceLast := by
            rw [unitSubdividePolyline_getLast?
              (by simp) orthogonalParts.2,
              sourceSecondLast]
          have sourceLastNotInFirst :
              sourceLast ∉ unitSubdividePolyline sourceFirst :=
            sourceFreshJoined.not_mem_left_of_joinAtEndpoint
              sourceFirstSubdividedLast
              sourceSecondSubdividedHead
              sourceSecondSubdividedLast
              sourceSecondSubdividedLength
          have scaledSecondFresh :
              LastNotInDropLast
                (unitSubdividePolyline
                  (scalePolyline (factor : Int) sourceSecond)) := by
            exact tailInduction second sourceSecondFresh
              orthogonalParts.2
          let scaledFirst : List Cell :=
            [Cell.scale (factor : Int) first,
              Cell.scale (factor : Int) second]
          let scaledSecond : List Cell :=
            scalePolyline (factor : Int) sourceSecond
          have scaledFirstOrthogonal :
              PeriodicOrthocrossing.OrthogonalPolyline scaledFirst := by
            simpa [scaledFirst,
              PeriodicOrthocrossing.OrthogonalPolyline] using
              scaledAligned
          have scaledSecondOrthogonal :
              PeriodicOrthocrossing.OrthogonalPolyline scaledSecond :=
            PeriodicOrthocrossing.OrthogonalPolyline.scalePolyline
              orthogonalParts.2 factorPositive
          have scaledFirstLast :
              scaledFirst.getLast? =
                some (Cell.scale (factor : Int) second) := by
            simp [scaledFirst]
          have scaledSecondHead :
              scaledSecond.head? =
                some (Cell.scale (factor : Int) second) := by
            simp [scaledSecond, sourceSecond]
          have scaledSecondLast :
              scaledSecond.getLast? =
                some (Cell.scale (factor : Int) sourceLast) := by
            simp [scaledSecond, sourceSecondLast]
          have scaledLastNotInFirst :
              Cell.scale (factor : Int) sourceLast ∉
                unitSubdividePolyline scaledFirst := by
            intro member
            apply sourceLastNotInFirst
            exact mem_unitSubdividePolyline_scale_reflect
              factorPositive sourceFirstOrthogonal member
          have scaledJoinedFresh :=
            scaledSecondFresh.unitSubdividePolyline_joinAtEndpoint
              (first := scaledFirst) (second := scaledSecond)
              (middle := Cell.scale (factor : Int) second)
              (last := Cell.scale (factor : Int) sourceLast)
              (by simp [scaledFirst])
              (by simp [scaledSecond, sourceSecond])
              scaledFirstOrthogonal scaledSecondOrthogonal
              scaledFirstLast scaledSecondHead scaledSecondLast
              scaledLastNotInFirst
          simpa [scaledFirst, scaledSecond, sourceSecond,
            scalePolyline, LeanTrominoes.joinAtEndpoint] using
            scaledJoinedFresh

end AxisDirection
end LeanTrominoes
