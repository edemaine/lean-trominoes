/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularTerminalFanPorts

/-!
# Fixed inward routes from the adapter frame to Figure 7

On the radius-22 adapter square, the eight compass directions occur exactly
at port indices `0, 11, …, 77`.  These are the canonical anchors for Figure
7's eight radius-12 boundary sites.

Each anchor follows its compass ray inward by ten units.  Axis directions
give one segment and diagonal directions use the existing unit staircase.
The eight resulting orthogonal routes have exact endpoints and pairwise
disjoint point sets.  The only remaining fan-side routing problem is therefore
to move each shape-dependent fan-facing port to its slot's fixed anchor while
preserving their common clockwise order.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing

/-- Radius-22 square-frame port aligned with one Figure 7 compass slot. -/
def retainedTerminalFanAnchorPort
    (slot : RetainedTerminalSlot) :
    RetainedTerminalAdapterPort :=
  ⟨11 * slot.val, by
    have slotLt := slot.isLt
    omega⟩

@[simp]
theorem retainedTerminalFanAnchorPort_val
    (slot : RetainedTerminalSlot) :
    (retainedTerminalFanAnchorPort slot).val =
      11 * slot.val :=
  rfl

/-- Different Figure 7 slots select different frame anchors. -/
theorem retainedTerminalFanAnchorPort_injective :
    Function.Injective retainedTerminalFanAnchorPort := by
  intro first second portsEqual
  apply Fin.ext
  have valuesEqual :
      11 * first.val = 11 * second.val :=
    congrArg Fin.val portsEqual
  omega

/-- The square-frame anchor is exactly the radius-22 compass point of its
Figure 7 slot. -/
theorem retainedTerminalFanAnchorPortOffset_eq_scale_unitVector :
    ∀ slot : RetainedTerminalSlot,
      retainedTerminalAdapterPortOffset
          (retainedTerminalFanAnchorPort slot) =
        Cell.scale retainedTerminalAdapterFrameRadius
          (angularPortOfIndex slot.val).unitVector := by
  native_decide

/-- Fixed orthogonal route from a radius-22 frame anchor inward to the
corresponding radius-12 Figure 7 boundary point. -/
def retainedTerminalFanAnchorRoute
    (slot : RetainedTerminalSlot) : List Cell :=
  compassRay
    (oppositePort (angularPortOfIndex slot.val))
    10
    (retainedTerminalAdapterPortOffset
      (retainedTerminalFanAnchorPort slot))

/-- Every fixed inward route starts at its square-frame anchor. -/
@[simp]
theorem retainedTerminalFanAnchorRoute_head?
    (slot : RetainedTerminalSlot) :
    (retainedTerminalFanAnchorRoute slot).head? =
      some
        (retainedTerminalAdapterPortOffset
          (retainedTerminalFanAnchorPort slot)) := by
  simp [retainedTerminalFanAnchorRoute]

/-- Every fixed inward route ends at its exact Figure 7 boundary offset. -/
@[simp]
theorem retainedTerminalFanAnchorRoute_getLast? :
    ∀ slot : RetainedTerminalSlot,
      (retainedTerminalFanAnchorRoute slot).getLast? =
        some (angularFanBoundaryOffset slot.val) := by
  native_decide

/-- Every fixed inward anchor route is orthogonal. -/
theorem retainedTerminalFanAnchorRoute_orthogonal
    (slot : RetainedTerminalSlot) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (retainedTerminalFanAnchorRoute slot) := by
  exact compassRay_orthogonal _ _ _

/-- The eight fixed inward routes have pairwise disjoint point sets. -/
theorem retainedTerminalFanAnchorRoute_pairwise_disjoint :
    ∀ first second : RetainedTerminalSlot,
      first ≠ second →
        List.Disjoint
          (retainedTerminalFanAnchorRoute first)
          (retainedTerminalFanAnchorRoute second) := by
  intro first second slotsNe
  rw [List.disjoint_left]
  intro point firstMember secondMember
  rcases point with ⟨pointX, pointY⟩
  fin_cases first <;>
    fin_cases second <;>
    simp_all [retainedTerminalFanAnchorRoute,
      retainedTerminalFanAnchorPort,
      retainedTerminalAdapterPortOffset,
      angularPortOfIndex, oppositePort,
      OccurrenceSplitRing.Port.unitVector,
      compassRay, diagonalStaircase,
      Cell.add, Cell.scale] <;>
    omega

/-- Translate a fixed inward route to an arbitrary variable center. -/
def retainedTerminalFanAnchorRouteAt
    (center : Cell)
    (slot : RetainedTerminalSlot) : List Cell :=
  (retainedTerminalFanAnchorRoute slot).map
    (Cell.add center)

/-- A centered inward route starts at its centered adapter-frame anchor. -/
@[simp]
theorem retainedTerminalFanAnchorRouteAt_head?
    (center : Cell)
    (slot : RetainedTerminalSlot) :
    (retainedTerminalFanAnchorRouteAt center slot).head? =
      some
        (Cell.add center
          (retainedTerminalAdapterPortOffset
            (retainedTerminalFanAnchorPort slot))) := by
  simp [retainedTerminalFanAnchorRouteAt]

/-- A centered inward route ends at the corresponding centered Figure 7
boundary point. -/
@[simp]
theorem retainedTerminalFanAnchorRouteAt_getLast?
    (center : Cell)
    (slot : RetainedTerminalSlot) :
    (retainedTerminalFanAnchorRouteAt center slot).getLast? =
      some
        (Cell.add center
          (angularFanBoundaryOffset slot.val)) := by
  simp [retainedTerminalFanAnchorRouteAt]

/-- Centering preserves orthogonality of every inward anchor route. -/
theorem retainedTerminalFanAnchorRouteAt_orthogonal
    (center : Cell)
    (slot : RetainedTerminalSlot) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (retainedTerminalFanAnchorRouteAt center slot) := by
  exact
    OccurrenceSplitRing.PeriodicOrthocrossing.OrthogonalPolyline.map_add
      (retainedTerminalFanAnchorRoute_orthogonal slot)
      center

/-- Centering preserves pairwise disjointness of the fixed inward routes. -/
theorem retainedTerminalFanAnchorRouteAt_pairwise_disjoint
    (center : Cell)
    (first second : RetainedTerminalSlot)
    (slotsNe : first ≠ second) :
    List.Disjoint
      (retainedTerminalFanAnchorRouteAt center first)
      (retainedTerminalFanAnchorRouteAt center second) := by
  simpa [retainedTerminalFanAnchorRouteAt] using
    (retainedTerminalFanAnchorRoute_pairwise_disjoint
      first second slotsNe).map
      (Cell.add_left_injective center)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
