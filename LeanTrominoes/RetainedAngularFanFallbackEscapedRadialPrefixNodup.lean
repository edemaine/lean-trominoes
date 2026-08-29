/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineStrictDirectionNodup
import LeanTrominoes.RetainedAngularFanFallbackEscapedRadialPrefixData
import LeanTrominoes.RetainedAngularFanFallbackExteriorRadialJoinNodup

/-! # Duplicate-freeness of escaped fallback radial prefixes -/

namespace LeanTrominoes

namespace Gadget

/-- Rebuilding a direction word commutes with translation of its start. -/
theorem rebuildRoute_add
    (offset start : Cell) (directions : List AxisDirection) :
    rebuildRoute (Cell.add offset start) directions =
      (rebuildRoute start directions).map (Cell.add offset) := by
  induction directions generalizing start with
  | nil => simp [rebuildRoute]
  | cons direction directions induction =>
      simp only [rebuildRoute, List.map_cons]
      congr 1
      rw [← induction (Cell.add start direction.step)]
      congr 1
      rcases offset with ⟨offsetX, offsetY⟩
      rcases start with ⟨startX, startY⟩
      rcases direction.step with ⟨stepX, stepY⟩
      simp [Cell.add]
      constructor <;> ring

end Gadget

namespace PeriodicEightOccurrenceSplit
namespace FallbackSuffixDirectionCompiler

open PeriodicOrthocrossing

/-- The fixed source-escape-and-lane-shift table has no repeated rebuilt
point at the origin. -/
private theorem escapedFixedPrefixDirections_rebuild_zero_nodup :
    ∀ (direction : RetainedTerminalDirection)
      (slot : RetainedTerminalSlot),
      (Gadget.rebuildRoute (0, 0)
        (prefixDirections .escaped direction slot)).Nodup := by
  native_decide

/-- Translating the start of the fixed escaped word preserves its
duplicate-freeness. -/
theorem escapedFixedPrefixDirections_rebuild_nodup
    (start : Cell)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) :
    (Gadget.rebuildRoute start
      (prefixDirections .escaped direction slot)).Nodup := by
  have translated :=
    (escapedFixedPrefixDirections_rebuild_zero_nodup direction slot).map
      (Cell.add_left_injective start)
  rw [← Gadget.rebuildRoute_add start (0, 0)] at translated
  simpa [Cell.add] using translated

/-- Every fixed positioned source escape plus delayed lane shift has
duplicate-free ordered unit subdivision. -/
theorem retainedTerminalFanOuterEscapedFixedPrefix_unitSubdivide_nodup
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    (AxisDirection.unitSubdividePolyline
      (retainedTerminalFanOuterEscapedFixedPrefix
        center terminal slot)).Nodup := by
  let route :=
    retainedTerminalFanOuterEscapedFixedPrefix center terminal slot
  let start :=
    (retainedAngularFanOuterDemand center terminal slot).gate
  change (AxisDirection.unitSubdividePolyline route).Nodup
  have routeHead : route.head? = some start :=
    retainedTerminalFanOuterEscapedFixedPrefix_head?
      center terminal slot
  have routeNonempty : route ≠ [] := by
    intro empty
    rw [empty] at routeHead
    simp at routeHead
  have routeOrthogonal : OrthogonalPolyline route :=
    retainedTerminalFanOuterEscapedFixedPrefix_orthogonal
      center terminal slot
  obtain ⟨first, rest, routeEq⟩ := List.exists_cons_of_ne_nil routeNonempty
  have firstEq : first = start := by
    simpa [routeEq] using routeHead
  subst first
  rw [routeEq,
    AxisDirection.unitSubdividePolyline_eq_rebuildRoute
      start rest (by simpa [routeEq] using routeOrthogonal)]
  have directionsEq :=
    retainedTerminalFanOuterEscapedFixedPrefix_directions
      center terminal slot
  change Gadget.unitSubdivisionDirections route = _ at directionsEq
  rw [routeEq] at directionsEq
  rw [directionsEq]
  exact escapedFixedPrefixDirections_rebuild_nodup
    start terminal.1 slot

/-- The fixed escaped word moves weakly inward in the radial join
functional. -/
theorem escapedPrefixDirections_join_nonnegative :
    ∀ (direction : RetainedTerminalDirection)
      (slot : RetainedTerminalSlot)
      (axis : AxisDirection),
      axis ∈ prefixDirections .escaped direction slot →
        0 ≤ Cell.linearValue
          (retainedFallbackRadialJoinNormal direction) axis.step := by
  native_decide

/-- Every subdivided fixed escaped-prefix point lies no farther inward than
its shifted endpoint. -/
theorem retainedTerminalFanOuterEscapedFixedPrefix_join_le_finish
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (point : Cell)
    (pointMember :
      point ∈ AxisDirection.unitSubdividePolyline
        (retainedTerminalFanOuterEscapedFixedPrefix
          center terminal slot)) :
    Cell.linearValue
        (retainedFallbackRadialJoinNormal terminal.1) point ≤
      Cell.linearValue
        (retainedFallbackRadialJoinNormal terminal.1)
        (Cell.add
          (retainedTerminalFanOuterSourceEscapePoint center terminal slot)
          (retainedTerminalFanOuterLaneOffset terminal.1 slot)) := by
  let route :=
    retainedTerminalFanOuterEscapedFixedPrefix center terminal slot
  have routeHead :
      route.head? =
        some
          (retainedAngularFanOuterDemand center terminal slot).gate :=
    retainedTerminalFanOuterEscapedFixedPrefix_head?
      center terminal slot
  have routeNonempty : route ≠ [] := by
    intro empty
    rw [empty] at routeHead
    simp at routeHead
  have routeOrthogonal : OrthogonalPolyline route :=
    retainedTerminalFanOuterEscapedFixedPrefix_orthogonal
      center terminal slot
  apply
    AxisDirection.unitSubdividePolyline_linear_le_last_of_direction_nonnegative
      routeNonempty routeOrthogonal
      (retainedFallbackRadialJoinNormal terminal.1)
  · intro axis axisMember
    have directionsEq :=
      retainedTerminalFanOuterEscapedFixedPrefix_directions
        center terminal slot
    rw [directionsEq] at axisMember
    exact escapedPrefixDirections_join_nonnegative
      terminal.1 slot axis axisMember
  · exact retainedTerminalFanOuterEscapedFixedPrefix_getLast?
      center terminal slot
  · exact pointMember

/-- Every escaped exterior radial prefix has duplicate-free ordered unit
subdivision, independently of its dynamic remaining length. -/
theorem retainedTerminalFanOuterEscapedRadialPrefix_unitSubdivide_nodup
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    (AxisDirection.unitSubdividePolyline
      (retainedTerminalFanOuterEscapedRadialPrefix
        center terminal slot)).Nodup := by
  let fixedPrefix :=
    retainedTerminalFanOuterEscapedFixedPrefix center terminal slot
  let shiftedPoint :=
    Cell.add
      (retainedTerminalFanOuterSourceEscapePoint center terminal slot)
      (retainedTerminalFanOuterLaneOffset terminal.1 slot)
  let count :=
    retainedTerminalFanOuterRadialLength terminal -
      retainedTerminalFanOuterSourceEscapeLength - 1
  let rayRoute :=
    (retainedTerminalFanOuterInwardRayOfLength
      terminal.1 count).rasterize shiftedPoint
  have routeEq :
      retainedTerminalFanOuterEscapedRadialPrefix center terminal slot =
        joinAtEndpoint fixedPrefix rayRoute := by
    simpa [fixedPrefix, shiftedPoint, count, rayRoute,
      retainedTerminalFanOuterEscapedRemainingPrefixRay] using
      retainedTerminalFanOuterEscapedRadialPrefix_eq_fixedPrefix_join
        center terminal slot
  have fixedHead :=
    retainedTerminalFanOuterEscapedFixedPrefix_head?
      center terminal slot
  have fixedNonempty : fixedPrefix ≠ [] := by
    intro empty
    change fixedPrefix.head? = _ at fixedHead
    rw [empty] at fixedHead
    simp at fixedHead
  have fixedLast : fixedPrefix.getLast? = some shiftedPoint := by
    exact retainedTerminalFanOuterEscapedFixedPrefix_getLast?
      center terminal slot
  have rayHead : rayRoute.head? = some shiftedPoint :=
    RetainedRay.rasterize_head? _ _
  have fixedNodup :
      (AxisDirection.unitSubdividePolyline fixedPrefix).Nodup :=
    retainedTerminalFanOuterEscapedFixedPrefix_unitSubdivide_nodup
      center terminal slot
  have rayNodup :
      (AxisDirection.unitSubdividePolyline rayRoute).Nodup := by
    exact retainedTerminalFanOuterInwardRayOfLength_unitSubdivide_nodup
      terminal.1 count shiftedPoint
  rw [routeEq,
    AxisDirection.unitSubdividePolyline_joinAtEndpoint
      fixedNonempty fixedLast rayHead,
    joinAtEndpoint]
  apply fixedNodup.append rayNodup.tail
  rw [List.disjoint_left]
  intro point fixedMember rayTailMember
  by_cases countZero : count = 0
  · unfold rayRoute at rayTailMember
    rw [countZero] at rayTailMember
    rcases terminal with ⟨direction, length⟩
    cases direction <;>
      simp [retainedTerminalFanOuterInwardRayOfLength,
        RetainedRay.rasterize, compassRay,
        routedClauseRay] at rayTailMember
  · have countPositive : 0 < count := Nat.pos_of_ne_zero countZero
    have fixedUpper :=
      retainedTerminalFanOuterEscapedFixedPrefix_join_le_finish
        center terminal slot point fixedMember
    have rayLower :
        Cell.linearValue
            (retainedFallbackRadialJoinNormal terminal.1)
            shiftedPoint <
          Cell.linearValue
            (retainedFallbackRadialJoinNormal terminal.1)
            point := by
      exact
        retainedTerminalFanOuterInwardRayOfLength_tail_join_gt_start
          terminal.1 count shiftedPoint point countPositive rayTailMember
    exact not_lt_of_ge fixedUpper rayLower

end FallbackSuffixDirectionCompiler
end PeriodicEightOccurrenceSplit
end LeanTrominoes
