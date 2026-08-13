/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanOuterRadialDecomposition
import LeanTrominoes.RetainedAngularFanOuterEscapedRoutes

/-!
# Splitting retained-ray rasterizations

Blocked retained rays list every primitive staircase block, so their
rasterizations split exactly after any requested number of blocks.  Cardinal
compass rays instead coarsen the same geometry to one segment; the
middle-point refinement theorem transports strict separation to either
subsegment.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Joining a singleton to a route with that head returns the route. -/
private theorem joinAtEndpoint_singleton_left_of_head
    {α : Type*} {start : α} {route : List α}
    (routeHead : route.head? = some start) :
    joinAtEndpoint [start] route = route := by
  cases route with
  | nil =>
      simp at routeHead
  | cons head tail =>
      simp only [List.head?_cons, Option.some.injEq] at routeHead
      subst head
      simp [joinAtEndpoint]

/-- Split a diagonal staircase after an arbitrary number of primitive
blocks. -/
theorem diagonalStaircase_split
    (horizontal vertical : Int)
    (prefixLength suffixLength : Nat)
    (start : Cell) :
    diagonalStaircase horizontal vertical
        (prefixLength + suffixLength) start =
      joinAtEndpoint
        (diagonalStaircase horizontal vertical prefixLength start)
        (diagonalStaircase horizontal vertical suffixLength
          (Cell.add start
            (Cell.scale prefixLength (horizontal, vertical)))) := by
  induction prefixLength generalizing start with
  | zero =>
      simpa [diagonalStaircase, Cell.add, Cell.scale] using
        (joinAtEndpoint_singleton_left_of_head
          (diagonalStaircase_head?
            horizontal vertical suffixLength start)).symm
  | succ prefixLength induction =>
      simp only [Nat.succ_add, diagonalStaircase]
      rw [induction]
      unfold joinAtEndpoint
      simp only [List.cons_append]
      have checkpointEq :
          Cell.add
              (Cell.add start (horizontal, vertical))
              (Cell.scale prefixLength (horizontal, vertical)) =
            Cell.add start
              (Cell.scale (prefixLength + 1)
                (horizontal, vertical)) := by
        apply Prod.ext <;>
          simp [Cell.add, Cell.scale] <;>
          ring
      rw [checkpointEq]
      norm_num

/-- Split a routed-clause staircase after an arbitrary number of primitive
blocks. -/
theorem routedClauseRay_split
    (arm : PlanarThreeSAT.DuplicatorArm)
    (prefixLength suffixLength : Nat)
    (start : Cell) :
    routedClauseRay arm (prefixLength + suffixLength) start =
      joinAtEndpoint
        (routedClauseRay arm prefixLength start)
        (routedClauseRay arm suffixLength
          (Cell.add start
            (Cell.scale prefixLength
              (routedClauseRayPrimitive arm)))) := by
  induction prefixLength generalizing start with
  | zero =>
      simpa [routedClauseRay, Cell.add, Cell.scale] using
        (joinAtEndpoint_singleton_left_of_head
          (routedClauseRay_head?
            arm suffixLength start)).symm
  | succ prefixLength induction =>
      simp only [Nat.succ_add, routedClauseRay]
      rw [induction]
      have checkpointEq :
          Cell.add
              (Cell.add start (routedClauseRayPrimitive arm))
              (Cell.scale prefixLength
                (routedClauseRayPrimitive arm)) =
            Cell.add start
              (Cell.scale (prefixLength + 1)
                (routedClauseRayPrimitive arm)) := by
        apply Prod.ext <;>
          simp [Cell.add, Cell.scale] <;>
          ring
      rw [checkpointEq]
      have middleNe :
          routedClauseRay arm prefixLength
              (Cell.add start
                (routedClauseRayPrimitive arm)) ≠ [] := by
        intro empty
        have head :=
          routedClauseRay_head? arm prefixLength
            (Cell.add start
              (routedClauseRayPrimitive arm))
        simp [empty] at head
      exact joinAtEndpoint_assoc_of_middle_ne_nil middleNe

/-- Every blocked retained-direction raster splits exactly after an
arbitrary number of primitive blocks. -/
theorem retainedTerminalFanOuterInwardRayOfLength_split_of_blocked
    (direction : RetainedTerminalDirection)
    (prefixLength suffixLength : Nat)
    (start : Cell)
    (blocked : direction.usesBlockedRaster) :
    (retainedTerminalFanOuterInwardRayOfLength direction
        (prefixLength + suffixLength)).rasterize start =
      joinAtEndpoint
        ((retainedTerminalFanOuterInwardRayOfLength
          direction prefixLength).rasterize start)
        ((retainedTerminalFanOuterInwardRayOfLength
          direction suffixLength).rasterize
            (Cell.add start
              (Cell.scale prefixLength
                (retainedTerminalFanOuterInwardRayOfLength
                  direction prefixLength).primitive))) := by
  cases direction with
  | compass port =>
      cases port <;>
        simp [RetainedTerminalDirection.usesBlockedRaster,
          portUsesDiagonalRaster,
          retainedTerminalFanOuterInwardRayOfLength,
          RetainedRay.rasterize, RetainedRay.primitive,
          oppositePort] at blocked ⊢ <;>
        exact diagonalStaircase_split _ _
          prefixLength suffixLength start
  | routedClause arm =>
      simpa [retainedTerminalFanOuterInwardRayOfLength,
        RetainedRay.rasterize, RetainedRay.primitive] using
        routedClauseRay_split arm prefixLength suffixLength start

/-- A positive cardinal compass ray is represented by its one direct
segment. -/
theorem compassRay_eq_two_points_of_not_diagonal
    (port : OccurrenceSplitRing.Port)
    (length : Nat)
    (start : Cell)
    (lengthPositive : 0 < length)
    (notDiagonal : ¬portUsesDiagonalRaster port) :
    compassRay port length start =
      [start,
        Cell.add start
          (Cell.scale length port.unitVector)] := by
  cases length with
  | zero =>
      omega
  | succ length =>
      cases port <;>
        simp [portUsesDiagonalRaster, compassRay]
          at notDiagonal ⊢

/-- A geometric suffix of a cardinal compass ray inherits strict
separation from the full (coarsened) segment. -/
theorem compassRay_suffix_strictlyAvoid_of_not_diagonal
    (port : OccurrenceSplitRing.Port)
    (prefixLength suffixLength : Nat)
    (start : Cell)
    (other : List Cell)
    (prefixPositive : 0 < prefixLength)
    (notDiagonal : ¬portUsesDiagonalRaster port)
    (strict :
      RoutesStrictlyAvoidEachOther
        (compassRay port (prefixLength + suffixLength) start)
        other) :
    RoutesStrictlyAvoidEachOther
      (compassRay port suffixLength
        (Cell.add start
          (Cell.scale prefixLength port.unitVector)))
      other := by
  rw [compassRay_eq_two_points_of_not_diagonal
    port (prefixLength + suffixLength) start
    (by omega) notDiagonal] at strict
  cases suffixLength with
  | zero =>
      simpa [compassRay] using
        strict.singleton_left (point := Cell.add start
          (Cell.scale prefixLength port.unitVector)) (by simp)
  | succ suffixLength =>
      let middle :=
        Cell.add start
          (Cell.scale prefixLength port.unitVector)
      let finish :=
        Cell.add start
          (Cell.scale (prefixLength + (suffixLength + 1))
            port.unitVector)
      have middleInterior :
          (GridSegment.mk start finish).InteriorContains middle := by
        rcases start with ⟨startX, startY⟩
        cases port <;>
          simp [portUsesDiagonalRaster] at notDiagonal
        all_goals
          simp [middle, finish,
            GridSegment.InteriorContains,
            GridSegment.IsHorizontal,
            GridSegment.IsVertical,
            GridSegment.StrictlyBetween,
            OccurrenceSplitRing.Port.unitVector,
            Cell.add, Cell.scale]
          omega
      have strictSegment :
          RoutesStrictlyAvoidEachOther
            [start, finish] other := by
        simpa [finish] using strict
      have refined :=
        strictSegment.refine_middle_left middleInterior
      have tail :=
        (refined.of_join_left
          (boundary := middle)
          (first := [start, middle])
          (extra := [middle, finish])
          (by simp) (by simp)).2
      rw [compassRay_eq_two_points_of_not_diagonal
        port (suffixLength + 1) middle
        (by omega) notDiagonal]
      have tailFinishEq :
          Cell.add middle
              (Cell.scale (suffixLength + 1) port.unitVector) =
            finish := by
        rcases start with ⟨startX, startY⟩
        apply Prod.ext <;>
          simp [middle, finish, Cell.add, Cell.scale] <;>
          ring
      norm_num at tailFinishEq ⊢
      rw [tailFinishEq]
      exact tail

/-- A suffix of any retained-direction raster inherits strict separation
from the full raster.  Blocked rays split exactly; cardinal rays refine
their single long segment at the suffix checkpoint. -/
theorem
    retainedTerminalFanOuterInwardRayOfLength_suffix_strictlyAvoid
    (direction : RetainedTerminalDirection)
    (prefixLength suffixLength : Nat)
    (start : Cell)
    (other : List Cell)
    (prefixPositive : 0 < prefixLength)
    (strict :
      RoutesStrictlyAvoidEachOther
        ((retainedTerminalFanOuterInwardRayOfLength direction
          (prefixLength + suffixLength)).rasterize start)
        other) :
    RoutesStrictlyAvoidEachOther
      ((retainedTerminalFanOuterInwardRayOfLength direction
        suffixLength).rasterize
          (Cell.add start
            (Cell.scale prefixLength
              (retainedTerminalFanOuterInwardRayOfLength
                direction prefixLength).primitive)))
      other := by
  by_cases blocked : direction.usesBlockedRaster
  · rw [
      retainedTerminalFanOuterInwardRayOfLength_split_of_blocked
        direction prefixLength suffixLength start blocked] at strict
    exact
      (strict.of_join_left
        (by
          rw [RetainedRay.rasterize_getLast?,
            RetainedRay.vector_eq_scale_length_primitive]
          cases direction <;>
            simp [retainedTerminalFanOuterInwardRayOfLength,
              RetainedRay.length])
        (RetainedRay.rasterize_head? _ _)).2
  · cases direction with
    | compass port =>
        exact compassRay_suffix_strictlyAvoid_of_not_diagonal
          (oppositePort port) prefixLength suffixLength
          start other prefixPositive
          (by
            cases port <;>
              simp [RetainedTerminalDirection.usesBlockedRaster,
                portUsesDiagonalRaster, oppositePort] at blocked ⊢)
          (by
            simpa [retainedTerminalFanOuterInwardRayOfLength,
              RetainedRay.rasterize] using strict)
    | routedClause arm =>
        simp [RetainedTerminalDirection.usesBlockedRaster] at blocked

end PeriodicEightOccurrenceSplit
end LeanTrominoes
