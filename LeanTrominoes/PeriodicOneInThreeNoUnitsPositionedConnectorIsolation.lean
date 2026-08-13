/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineUnitSubdivisionContacts
import LeanTrominoes.PeriodicOneInThreeNoUnitsPositionedInheritedRouteIsolation
import LeanTrominoes.PositionedPeriodicCNFOrthogonalDetourTranslation

/-!
# Unit-elimination connector isolation

The inherited unit-elimination connector runs from one of the three fixed
boundary ports to the first point of a sixfold-refined source route.  Its two
outer detour coordinates are one unit off the refined source lattice.  Thus a
refined source-lattice point on the connector must already lie on the source
route's first segment.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreeNoUnitsPositioned

/-- A canonical Manhattan detour has an isolated target whenever the target
does not already lie on the detour's first horizontal segment.  The other
three prefix segments use coordinates strictly beyond the target. -/
theorem orthogonalDetour_lastNotInDropLast_of_targetOutsideFirst
    (source target : Cell)
    (targetOutside :
      ¬(GridSegment.mk source
        (PositionedPeriodicCNF.freshDetourCoordinate
          source.1 target.1, source.2)).Contains target) :
    AxisDirection.LastNotInDropLast
      (AxisDirection.unitSubdividePolyline
        (PositionedPeriodicCNF.orthogonalDetour source target)) := by
  let detourX :=
    PositionedPeriodicCNF.freshDetourCoordinate source.1 target.1
  let detourY :=
    PositionedPeriodicCNF.freshDetourCoordinate source.2 target.2
  let connectorPrefix : List Cell :=
    [source, (detourX, source.2), (detourX, detourY),
      (target.1, detourY)]
  let finalSegment : List Cell :=
    [(target.1, detourY), target]
  have connectorSplit :
      PositionedPeriodicCNF.orthogonalDetour source target =
        joinAtEndpoint connectorPrefix finalSegment := by
    simp [PositionedPeriodicCNF.orthogonalDetour,
      connectorPrefix, finalSegment, detourX, detourY, joinAtEndpoint]
  have connectorOrthogonal :=
    PositionedPeriodicCNF.orthogonalDetour_orthogonal source target
  have prefixOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline connectorPrefix := by
    rcases source with ⟨sourceX, sourceY⟩
    rcases target with ⟨targetX, targetY⟩
    simp [connectorPrefix, detourX, detourY,
      PeriodicOrthocrossing.OrthogonalPolyline,
      GridSegment.IsAxisAligned, GridSegment.IsHorizontal,
      GridSegment.IsVertical,
      PositionedPeriodicCNF.freshDetourCoordinate]
    omega
  have finalOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline finalSegment := by
    rcases source with ⟨sourceX, sourceY⟩
    rcases target with ⟨targetX, targetY⟩
    simp [finalSegment, detourY,
      PeriodicOrthocrossing.OrthogonalPolyline,
      GridSegment.IsAxisAligned, GridSegment.IsHorizontal,
      GridSegment.IsVertical,
      PositionedPeriodicCNF.freshDetourCoordinate]
    omega
  have finalFresh :
      AxisDirection.LastNotInDropLast
        (AxisDirection.unitSubdividePolyline finalSegment) := by
    apply AxisDirection.lastNotInDropLast_of_nodup
    simpa [finalSegment, AxisDirection.unitSubdividePolyline,
      joinAtEndpoint] using
      AxisDirection.unitSegmentPoints_nodup
        (List.isChain_cons_cons.mp finalOrthogonal).1
  have targetNotInPrefix :
      target ∉ AxisDirection.unitSubdividePolyline connectorPrefix := by
    intro targetMember
    rcases
        AxisDirection.unitSubdividePolyline_mem_original_or_segmentInterior
          prefixOrthogonal targetMember with
      listed | ⟨segment, segmentMember, interior⟩
    · rcases source with ⟨sourceX, sourceY⟩
      rcases target with ⟨targetX, targetY⟩
      simp [GridSegment.Contains, GridSegment.IsHorizontal,
        GridSegment.IsVertical, GridSegment.Between,
        PositionedPeriodicCNF.freshDetourCoordinate] at targetOutside
      simp [connectorPrefix, detourX, detourY,
        PositionedPeriodicCNF.freshDetourCoordinate] at listed
      omega
    · rcases source with ⟨sourceX, sourceY⟩
      rcases target with ⟨targetX, targetY⟩
      simp [GridSegment.Contains, GridSegment.IsHorizontal,
        GridSegment.IsVertical, GridSegment.Between,
        PositionedPeriodicCNF.freshDetourCoordinate] at targetOutside
      simp [connectorPrefix, detourX, detourY,
        gridPolylineSegments] at segmentMember
      rcases segmentMember with rfl | rfl | rfl
      all_goals
        (simp [GridSegment.InteriorContains,
          GridSegment.IsHorizontal, GridSegment.IsVertical,
          GridSegment.StrictlyBetween,
          PositionedPeriodicCNF.freshDetourCoordinate] at interior <;>
        omega)
  rw [connectorSplit]
  apply
    AxisDirection.LastNotInDropLast.unitSubdividePolyline_joinAtEndpoint
      (middle := (target.1, detourY)) (last := target) finalFresh
  · simp [connectorPrefix]
  · simp [finalSegment]
  · exact prefixOrthogonal
  · exact finalOrthogonal
  · simp [connectorPrefix]
  · simp [finalSegment]
  · simp [finalSegment]
  · exact targetNotInPrefix

/-- A connector to a point on the scaled vertical source axis has an
isolated final endpoint for each of the three unit-elimination ports. -/
theorem sourcePortDetour_lastNotInDropLast_of_vertical
    (sourceLiteralIndex : Nat)
    (sourceLiteralIndexLt : sourceLiteralIndex < 3)
    (sourceExit : Cell)
    (sourceExitVertical : sourceExit.1 = 0) :
    AxisDirection.LastNotInDropLast
      (AxisDirection.unitSubdividePolyline
        (PositionedPeriodicCNF.orthogonalDetour
          (PlanarOneInThreeNoUnits.sourceLocalPosition
            sourceLiteralIndex)
          (Cell.scale gadgetScale sourceExit))) := by
  apply orthogonalDetour_lastNotInDropLast_of_targetOutsideFirst
  rcases sourceExit with ⟨sourceExitX, sourceExitY⟩
  simp only at sourceExitVertical
  subst sourceExitX
  interval_cases sourceLiteralIndex <;>
    simp [PlanarOneInThreeNoUnits.sourceLocalPosition,
      gadgetScale, Cell.scale,
      PositionedPeriodicCNF.freshDetourCoordinate,
      GridSegment.Contains, GridSegment.IsHorizontal,
      GridSegment.IsVertical, GridSegment.Between] <;>
    omega

/-- The vertical-target connector certificate is preserved by the common
anchor-gauge translation. -/
theorem shiftedSourcePortDetour_lastNotInDropLast_of_vertical
    (offset : Cell)
    (sourceLiteralIndex : Nat)
    (sourceLiteralIndexLt : sourceLiteralIndex < 3)
    (sourceExit : Cell)
    (sourceExitVertical : sourceExit.1 = 0) :
    AxisDirection.LastNotInDropLast
      (AxisDirection.unitSubdividePolyline
        (PositionedPeriodicCNF.orthogonalDetour
          (Cell.add offset
            (PlanarOneInThreeNoUnits.sourceLocalPosition
              sourceLiteralIndex))
          (Cell.add offset (Cell.scale gadgetScale sourceExit)))) := by
  rw [PositionedPeriodicCNF.orthogonalDetour_add_left]
  exact
    (sourcePortDetour_lastNotInDropLast_of_vertical
      sourceLiteralIndex sourceLiteralIndexLt sourceExit
      sourceExitVertical).unitSubdividePolyline_map_add offset

/-- A scaled lattice point outside the source route's first segment cannot
occur on the unit-subdivided boundary-port detour to its scaled first exit. -/
theorem scaledPoint_not_mem_sourcePortDetour
    (sourceLiteralIndex : Nat)
    (sourceLiteralIndexLt : sourceLiteralIndex < 3)
    (sourceExit sourcePoint : Cell)
    (firstAligned :
      (GridSegment.mk (0, 0) sourceExit).IsAxisAligned)
    (sourcePointOutside :
      ¬(GridSegment.mk (0, 0) sourceExit).Contains sourcePoint) :
    Cell.scale gadgetScale sourcePoint ∉
      AxisDirection.unitSubdividePolyline
        (PositionedPeriodicCNF.orthogonalDetour
          (PlanarOneInThreeNoUnits.sourceLocalPosition
            sourceLiteralIndex)
          (Cell.scale gadgetScale sourceExit)) := by
  intro pointMember
  have connectorOrthogonal :=
    PositionedPeriodicCNF.orthogonalDetour_orthogonal
      (PlanarOneInThreeNoUnits.sourceLocalPosition
        sourceLiteralIndex)
      (Cell.scale gadgetScale sourceExit)
  rcases
      AxisDirection.unitSubdividePolyline_mem_original_or_segmentInterior
        connectorOrthogonal pointMember with
    originalMember | ⟨segment, segmentMember, interior⟩
  · rcases sourceExit with ⟨exitX, exitY⟩
    rcases sourcePoint with ⟨pointX, pointY⟩
    simp only [GridSegment.IsAxisAligned,
      GridSegment.IsHorizontal, GridSegment.IsVertical] at firstAligned
    rcases firstAligned with
      ⟨horizontal, nondegenerate⟩ | ⟨vertical, nondegenerate⟩
    all_goals
      interval_cases sourceLiteralIndex <;>
        simp [PositionedPeriodicCNF.orthogonalDetour,
          PositionedPeriodicCNF.freshDetourCoordinate,
          PlanarOneInThreeNoUnits.sourceLocalPosition,
          gadgetScale, Cell.scale] at originalMember
    all_goals
      apply sourcePointOutside
      simp [GridSegment.Contains, GridSegment.IsHorizontal,
        GridSegment.IsVertical, GridSegment.Between]
      omega
  · rcases sourceExit with ⟨exitX, exitY⟩
    rcases sourcePoint with ⟨pointX, pointY⟩
    simp only [GridSegment.IsAxisAligned,
      GridSegment.IsHorizontal, GridSegment.IsVertical] at firstAligned
    rcases firstAligned with
      ⟨horizontal, nondegenerate⟩ | ⟨vertical, nondegenerate⟩
    all_goals
      interval_cases sourceLiteralIndex <;>
        simp [PositionedPeriodicCNF.orthogonalDetour,
          PositionedPeriodicCNF.freshDetourCoordinate,
          PlanarOneInThreeNoUnits.sourceLocalPosition,
          gadgetScale, Cell.scale,
          gridPolylineSegments] at segmentMember
    all_goals
      rcases segmentMember with rfl | rfl | rfl | rfl
      all_goals
        simp [GridSegment.InteriorContains,
          GridSegment.IsHorizontal, GridSegment.IsVertical,
          GridSegment.StrictlyBetween, gadgetScale,
          Cell.scale] at interior
        apply sourcePointOutside
        simp [GridSegment.Contains, GridSegment.IsHorizontal,
          GridSegment.IsVertical, GridSegment.Between]
        omega

/-- If an endpoint-isolated source route already ends at its first exit,
then it consists of exactly that one segment. -/
theorem eq_pair_of_last_eq_firstExit
    {sourceRoute : List Cell} {sourceHead sourceExit : Cell}
    (sourceRouteHead : sourceRoute.head? = some sourceHead)
    (sourceRouteExit : sourceRoute.tail.head? = some sourceExit)
    (sourceRouteLast : sourceRoute.getLast? = some sourceExit)
    (sourceOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline sourceRoute)
    (sourceFresh :
      AxisDirection.LastNotInDropLast
        (AxisDirection.unitSubdividePolyline sourceRoute)) :
    sourceRoute = [sourceHead, sourceExit] := by
  cases sourceRoute with
  | nil => simp at sourceRouteHead
  | cons actualHead rest =>
      have actualHeadEqual : actualHead = sourceHead := by
        simpa using sourceRouteHead
      subst actualHead
      cases rest with
      | nil => simp at sourceRouteExit
      | cons actualExit rest =>
          have actualExitEqual : actualExit = sourceExit := by
            simpa using sourceRouteExit
          subst actualExit
          cases rest with
          | nil => rfl
          | cons third tail =>
              let first : List Cell := [sourceHead, sourceExit]
              let second : List Cell := sourceExit :: third :: tail
              have firstLast : first.getLast? = some sourceExit := by
                simp [first]
              have secondHead : second.head? = some sourceExit := by
                simp [second]
              have split :=
                AxisDirection.unitSubdividePolyline_joinAtEndpoint
                  (first := first) (second := second)
                  (firstNonempty := by simp [first])
                  (firstLast := firstLast)
                  (secondHead := secondHead)
              have joinedFresh :
                  AxisDirection.LastNotInDropLast
                    (joinAtEndpoint
                      (AxisDirection.unitSubdividePolyline first)
                      (AxisDirection.unitSubdividePolyline second)) := by
                rw [← split]
                simpa [first, second, joinAtEndpoint] using sourceFresh
              have firstOrthogonal :
                  PeriodicOrthocrossing.OrthogonalPolyline first := by
                simpa [first,
                  PeriodicOrthocrossing.OrthogonalPolyline] using
                  (List.isChain_cons_cons.mp sourceOrthogonal).1
              have secondOrthogonal :
                  PeriodicOrthocrossing.OrthogonalPolyline second := by
                exact (List.isChain_cons_cons.mp sourceOrthogonal).2
              have firstSubdividedLast :
                  (AxisDirection.unitSubdividePolyline first).getLast? =
                    some sourceExit := by
                rw [AxisDirection.unitSubdividePolyline_getLast?
                  (by simp [first]) firstOrthogonal, firstLast]
              have secondSubdividedHead :
                  (AxisDirection.unitSubdividePolyline second).head? =
                    some sourceExit := by
                rw [AxisDirection.unitSubdividePolyline_head?
                  (by simp [second]), secondHead]
              have secondSubdividedLast :
                  (AxisDirection.unitSubdividePolyline second).getLast? =
                    some sourceExit := by
                rw [AxisDirection.unitSubdividePolyline_getLast?
                  (by simp [second]) secondOrthogonal]
                simpa [second] using sourceRouteLast
              have secondSubdividedLength :
                  2 ≤
                    (AxisDirection.unitSubdividePolyline second).length :=
                AxisDirection.unitSubdividePolyline_length_ge_two_of_length_ge_two
                  (by simp [second]) secondOrthogonal
              have sourceExitNotInFirst :
                  sourceExit ∉
                    AxisDirection.unitSubdividePolyline first :=
                joinedFresh.not_mem_left_of_joinAtEndpoint
                  firstSubdividedLast secondSubdividedHead
                  secondSubdividedLast secondSubdividedLength
              exact (sourceExitNotInFirst
                (List.mem_of_mem_getLast? firstSubdividedLast)).elim

/-- The source route's isolated final endpoint lies outside its first closed
segment unless that first exit is already the final endpoint. -/
theorem firstSegment_not_contains_finalEndpoint
    {sourceRoute : List Cell} {sourceHead sourceExit sourceLast : Cell}
    (sourceRouteHead : sourceRoute.head? = some sourceHead)
    (sourceRouteExit : sourceRoute.tail.head? = some sourceExit)
    (sourceRouteLast : sourceRoute.getLast? = some sourceLast)
    (sourceLastNeExit : sourceLast ≠ sourceExit)
    (sourceOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline sourceRoute)
    (sourceFresh :
      AxisDirection.LastNotInDropLast
        (AxisDirection.unitSubdividePolyline sourceRoute)) :
    ¬(GridSegment.mk sourceHead sourceExit).Contains sourceLast := by
  intro contains
  cases sourceRoute with
  | nil => simp at sourceRouteHead
  | cons actualHead rest =>
      have actualHeadEqual : actualHead = sourceHead := by
        simpa using sourceRouteHead
      subst actualHead
      cases rest with
      | nil => simp at sourceRouteExit
      | cons actualExit rest =>
          have actualExitEqual : actualExit = sourceExit := by
            simpa using sourceRouteExit
          subst actualExit
          cases rest with
          | nil =>
              have sourceLastEqual : sourceLast = sourceExit := by
                simpa using sourceRouteLast.symm
              exact sourceLastNeExit sourceLastEqual
          | cons third tail =>
              let first : List Cell := [sourceHead, sourceExit]
              let second : List Cell := sourceExit :: third :: tail
              have firstLast : first.getLast? = some sourceExit := by
                simp [first]
              have secondHead : second.head? = some sourceExit := by
                simp [second]
              have split :=
                AxisDirection.unitSubdividePolyline_joinAtEndpoint
                  (first := first) (second := second)
                  (firstNonempty := by simp [first])
                  (firstLast := firstLast)
                  (secondHead := secondHead)
              have joinedFresh :
                  AxisDirection.LastNotInDropLast
                    (joinAtEndpoint
                      (AxisDirection.unitSubdividePolyline first)
                      (AxisDirection.unitSubdividePolyline second)) := by
                rw [← split]
                simpa [first, second, joinAtEndpoint] using sourceFresh
              have firstOrthogonal :
                  PeriodicOrthocrossing.OrthogonalPolyline first := by
                simpa [first,
                  PeriodicOrthocrossing.OrthogonalPolyline] using
                  (List.isChain_cons_cons.mp sourceOrthogonal).1
              have secondOrthogonal :
                  PeriodicOrthocrossing.OrthogonalPolyline second := by
                exact
                  (List.isChain_cons_cons.mp sourceOrthogonal).2
              have firstSubdividedLast :
                  (AxisDirection.unitSubdividePolyline first).getLast? =
                    some sourceExit := by
                rw [AxisDirection.unitSubdividePolyline_getLast?
                  (by simp [first]) firstOrthogonal, firstLast]
              have secondSubdividedHead :
                  (AxisDirection.unitSubdividePolyline second).head? =
                    some sourceExit := by
                rw [AxisDirection.unitSubdividePolyline_head?
                  (by simp [second]), secondHead]
              have secondSubdividedLast :
                  (AxisDirection.unitSubdividePolyline second).getLast? =
                    some sourceLast := by
                rw [AxisDirection.unitSubdividePolyline_getLast?
                  (by simp [second]) secondOrthogonal]
                simpa [second] using sourceRouteLast
              have secondSubdividedLength :
                  2 ≤
                    (AxisDirection.unitSubdividePolyline second).length :=
                AxisDirection.unitSubdividePolyline_length_ge_two_of_length_ge_two
                  (by simp [second]) secondOrthogonal
              have sourceLastNotInFirst :
                  sourceLast ∉
                    AxisDirection.unitSubdividePolyline first :=
                joinedFresh.not_mem_left_of_joinAtEndpoint
                  firstSubdividedLast secondSubdividedHead
                  secondSubdividedLast secondSubdividedLength
              apply sourceLastNotInFirst
              exact AxisDirection.mem_unitSubdividePolyline_of_segment_contains
                firstOrthogonal (by simp [first, gridPolylineSegments])
                contains

/-- The connector exclusion is equivariant under the common anchor-gauge
translation used by the positioned construction. -/
theorem shiftedScaledPoint_not_mem_sourcePortDetour
    (offset : Cell)
    (sourceLiteralIndex : Nat)
    (sourceLiteralIndexLt : sourceLiteralIndex < 3)
    (sourceExit sourcePoint : Cell)
    (firstAligned :
      (GridSegment.mk (0, 0) sourceExit).IsAxisAligned)
    (sourcePointOutside :
      ¬(GridSegment.mk (0, 0) sourceExit).Contains sourcePoint) :
    Cell.add offset (Cell.scale gadgetScale sourcePoint) ∉
      AxisDirection.unitSubdividePolyline
        (PositionedPeriodicCNF.orthogonalDetour
          (Cell.add offset
            (PlanarOneInThreeNoUnits.sourceLocalPosition
              sourceLiteralIndex))
          (Cell.add offset (Cell.scale gadgetScale sourceExit))) := by
  intro member
  rw [PositionedPeriodicCNF.orthogonalDetour_add_left,
    AxisDirection.unitSubdividePolyline_map_add] at member
  rcases List.mem_map.mp member with
    ⟨original, originalMember, translatedEqual⟩
  have originalEqual :
      original = Cell.scale gadgetScale sourcePoint := by
    apply Cell.add_left_injective offset
    exact translatedEqual
  subst original
  exact
    scaledPoint_not_mem_sourcePortDetour
      sourceLiteralIndex sourceLiteralIndexLt
      sourceExit sourcePoint firstAligned sourcePointOutside
      originalMember

end PeriodicOneInThreeNoUnitsPositioned
end LeanTrominoes
