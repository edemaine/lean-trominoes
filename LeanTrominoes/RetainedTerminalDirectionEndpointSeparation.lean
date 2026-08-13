/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineEndpointDirectionSeparation
import LeanTrominoes.RetainedTerminalDirections

/-!
# Retained terminal directions at a shared endpoint

Continuously separated orthogonal retained routes that finish at the same
point cannot have the same classified backwards terminal direction.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Two continuously separated orthogonal retained routes entering the same
endpoint have different classified terminal directions. -/
theorem retainedTerminalDirections_ne_of_routesAvoidEachOther
    {first second : List Cell}
    {firstDirection secondDirection : RetainedTerminalDirection}
    {firstTerminalLength secondTerminalLength : Nat}
    (firstLength : 2 ≤ first.length)
    (secondLength : 2 ≤ second.length)
    (firstOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline first)
    (secondOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline second)
    (sameFinish : first.getLast? = second.getLast?)
    (avoid : RoutesAvoidEachOther first second)
    (firstClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector first) =
        some (firstDirection, firstTerminalLength))
    (secondClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector second) =
        some (secondDirection, secondTerminalLength)) :
    firstDirection ≠ secondDirection := by
  have lastDirectionsDifferent :=
    polylineLastDirections_ne_of_routesAvoidEachOther
      firstLength secondLength firstOrthogonal secondOrthogonal
      sameFinish avoid
  intro directionsEqual
  apply lastDirectionsDifferent
  rcases AxisDirection.exists_eq_append_pair_of_length_ge_two
      firstLength with
    ⟨firstLeading, firstBefore, firstLast, firstEq⟩
  rcases AxisDirection.exists_eq_append_pair_of_length_ge_two
      secondLength with
    ⟨secondLeading, secondBefore, secondLast, secondEq⟩
  subst first
  subst second
  have firstAligned :
      (GridSegment.mk firstBefore firstLast).IsAxisAligned := by
    rw [PeriodicOrthocrossing.orthogonalPolyline_iff_segments]
      at firstOrthogonal
    apply firstOrthogonal
    rw [show firstLeading ++ [firstBefore, firstLast] =
        (firstLeading ++ [firstBefore]) ++ [firstLast] by simp]
    rw [gridPolylineSegments_append_singleton_of_ne_nil
      (firstLeading ++ [firstBefore]) (0, 0) firstLast]
    · simp
    · simp
  have secondAligned :
      (GridSegment.mk secondBefore secondLast).IsAxisAligned := by
    rw [PeriodicOrthocrossing.orthogonalPolyline_iff_segments]
      at secondOrthogonal
    apply secondOrthogonal
    rw [show secondLeading ++ [secondBefore, secondLast] =
        (secondLeading ++ [secondBefore]) ++ [secondLast] by simp]
    rw [gridPolylineSegments_append_singleton_of_ne_nil
      (secondLeading ++ [secondBefore]) (0, 0) secondLast]
    · simp
    · simp
  have firstClassification :=
    retainedTerminalDirectionClassify_sound firstClassified
  have secondClassification :=
    retainedTerminalDirectionClassify_sound secondClassified
  have firstPositive := firstClassification.1
  have secondPositive := secondClassification.1
  have firstSound := firstClassification.2
  have secondSound := secondClassification.2
  have firstVector :
      routeTerminalVector
          (firstLeading ++ [firstBefore, firstLast]) =
        Cell.sub firstBefore firstLast := by
    rw [show firstLeading ++ [firstBefore, firstLast] =
        (firstLeading ++ [firstBefore]) ++ [firstLast] by
      simp only [List.append_assoc, List.cons_append, List.nil_append]]
    unfold routeTerminalVector
    rw [gridPolylineSegments_append_singleton_of_ne_nil
      (firstLeading ++ [firstBefore]) (0, 0) firstLast (by simp)]
    simp [List.getLastD_eq_getLast?]
  have secondVector :
      routeTerminalVector
          (secondLeading ++ [secondBefore, secondLast]) =
        Cell.sub secondBefore secondLast := by
    rw [show secondLeading ++ [secondBefore, secondLast] =
        (secondLeading ++ [secondBefore]) ++ [secondLast] by
      simp only [List.append_assoc, List.cons_append, List.nil_append]]
    unfold routeTerminalVector
    rw [gridPolylineSegments_append_singleton_of_ne_nil
      (secondLeading ++ [secondBefore]) (0, 0) secondLast (by simp)]
    simp [List.getLastD_eq_getLast?]
  rw [firstVector] at firstSound
  rw [secondVector] at secondSound
  rw [show firstLeading ++ [firstBefore, firstLast] =
      (firstLeading ++ [firstBefore]) ++ [firstLast] by
    simp only [List.append_assoc, List.cons_append, List.nil_append]]
  rw [show secondLeading ++ [secondBefore, secondLast] =
      (secondLeading ++ [secondBefore]) ++ [secondLast] by
    simp only [List.append_assoc, List.cons_append, List.nil_append]]
  rw [AxisDirection.polylineLastDirection]
  rw [AxisDirection.polylineLastDirection]
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append]
  change
    (AxisDirection.between firstLast firstBefore).opposite =
      (AxisDirection.between secondLast secondBefore).opposite
  rw [AxisDirection.between_reverse_eq_opposite
    (AxisDirection.between_isGenuine_of_axisAligned firstAligned)]
  rw [AxisDirection.between_reverse_eq_opposite
    (AxisDirection.between_isGenuine_of_axisAligned secondAligned)]
  simp only [AxisDirection.opposite_opposite]
  subst secondDirection
  rcases firstBefore with ⟨firstBeforeX, firstBeforeY⟩
  rcases firstLast with ⟨firstLastX, firstLastY⟩
  rcases secondBefore with ⟨secondBeforeX, secondBeforeY⟩
  rcases secondLast with ⟨secondLastX, secondLastY⟩
  cases firstDirection with
  | compass port =>
      cases port <;>
        simp only [RetainedTerminalDirection.primitive, Port.unitVector,
          Cell.sub, Cell.scale, GridSegment.IsAxisAligned,
          GridSegment.IsHorizontal, GridSegment.IsVertical,
          Prod.mk.injEq, mul_zero, mul_one, mul_neg] at firstSound secondSound firstAligned secondAligned
      all_goals first
        | rw [
            (AxisDirection.between_eq_east_iff _ _).2 (by omega),
            (AxisDirection.between_eq_east_iff _ _).2 (by omega)]
        | rw [
            (AxisDirection.between_eq_north_iff _ _).2 (by omega),
            (AxisDirection.between_eq_north_iff _ _).2 (by omega)]
        | rw [
            (AxisDirection.between_eq_west_iff _ _).2 (by omega),
            (AxisDirection.between_eq_west_iff _ _).2 (by omega)]
        | rw [
            (AxisDirection.between_eq_south_iff _ _).2 (by omega),
            (AxisDirection.between_eq_south_iff _ _).2 (by omega)]
  | routedClause arm =>
      cases arm <;>
        simp only [RetainedTerminalDirection.primitive,
          routedClauseRayPrimitive, Cell.sub, Cell.scale,
          GridSegment.IsAxisAligned, GridSegment.IsHorizontal,
          GridSegment.IsVertical, Prod.mk.injEq] at firstSound secondSound firstAligned secondAligned <;>
        omega

end PeriodicEightOccurrenceSplit
end LeanTrominoes
