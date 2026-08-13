/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonClauseOuterFans

/-!
# Rank characterization of coordinated ribbon-fan orders

The finite endpoint routers are indexed by an explicit table of 28 direction
lists.  Downstream source constructions should not need to reason about that
table directly.  This file replaces membership in the table by the usual
cyclic-order condition on three cardinal directions.

All ordered pairs of distinct genuine directions are supported, so cyclic
order matters only when all three endpoint bundles are active.
-/

namespace LeanTrominoes

namespace AxisDirection

/-- Clockwise rank beginning at east.  The invalid fallback lies outside the
four genuine ranks. -/
def clockwiseRank : AxisDirection → Nat
  | .east => 0
  | .south => 1
  | .west => 2
  | .north => 3
  | .invalid => 4

/-- Three directions occur in clockwise cyclic order when some cyclic
rotation of their ranks is strictly increasing. -/
def InClockwiseOrder
    (first second third : AxisDirection) : Prop :=
  (first.clockwiseRank < second.clockwiseRank ∧
      second.clockwiseRank < third.clockwiseRank) ∨
    (second.clockwiseRank < third.clockwiseRank ∧
      third.clockwiseRank < first.clockwiseRank) ∨
    (third.clockwiseRank < first.clockwiseRank ∧
      first.clockwiseRank < second.clockwiseRank)

instance (first second third : AxisDirection) :
    Decidable (InClockwiseOrder first second third) := by
  unfold InClockwiseOrder
  infer_instance

/-- A genuine cardinal direction has one of the four clockwise ranks. -/
theorem clockwiseRank_lt_four
    {direction : AxisDirection}
    (genuine : direction.IsGenuine) :
    direction.clockwiseRank < 4 := by
  cases direction <;>
    simp_all [IsGenuine, clockwiseRank]

end AxisDirection

namespace PeriodicPlanarOneInThreeToThreeDM

namespace VariableOuterFanData

/-- The slot-indexed validity predicate is equivalently genuine,
duplicate-free membership of the displayed active direction list. -/
theorem isValid_iff_activeDirections
    (data : VariableOuterFanData) :
    data.IsValid ↔
      (∀ direction ∈ data.activeDirections,
          direction.IsGenuine) ∧
        data.activeDirections.Nodup := by
  native_decide +revert

/-- Membership in the 28-entry variable-fan table is exactly validity plus
the one cyclic-order condition needed in the three-slot case. -/
theorem isClockwiseCompatible_iff
    (data : VariableOuterFanData) :
    data.IsClockwiseCompatible ↔
      data.IsValid ∧
        (data.count = 3 →
          AxisDirection.InClockwiseOrder
            (data.direction .first)
            (data.direction .second)
            (data.direction .third)) := by
  native_decide +revert

/-- A valid one- or two-slot variable fan is automatically supported by the
finite routing table. -/
theorem isClockwiseCompatible_of_count_ne_three
    (data : VariableOuterFanData)
    (valid : data.IsValid)
    (count : data.count ≠ 3) :
    data.IsClockwiseCompatible :=
  (isClockwiseCompatible_iff data).2
    ⟨valid, fun countThree => (count countThree).elim⟩

/-- A valid three-slot variable fan is supported once its displayed
directions have the clockwise cyclic order. -/
theorem isClockwiseCompatible_of_three
    (data : VariableOuterFanData)
    (valid : data.IsValid)
    (clockwise :
      AxisDirection.InClockwiseOrder
        (data.direction .first)
        (data.direction .second)
        (data.direction .third)) :
    data.IsClockwiseCompatible :=
  (isClockwiseCompatible_iff data).2
    ⟨valid, fun _ => clockwise⟩

end VariableOuterFanData

namespace ClauseRibbonFanData

/-- Clause-fan table membership has the same direct characterization in
literal order: active directions are valid, and a ternary clause's
`top, left, right` directions occur clockwise. -/
theorem isClockwiseCompatible_iff
    (data : ClauseRibbonFanData) :
    data.IsClockwiseCompatible ↔
      (∀ group, data.GroupActive group →
          (data.direction group).IsGenuine) ∧
        (∀ first second,
          data.GroupActive first →
          data.GroupActive second →
          first ≠ second →
          data.direction first ≠ data.direction second) ∧
        (data.hasRight = true →
          AxisDirection.InClockwiseOrder
            (data.direction .top)
            (data.direction .left)
            (data.direction .right)) := by
  native_decide +revert

/-- A valid binary clause fan is automatically supported by the finite
routing table. -/
theorem isClockwiseCompatible_of_no_right
    (data : ClauseRibbonFanData)
    (genuine :
      ∀ group, data.GroupActive group →
        (data.direction group).IsGenuine)
    (distinct :
      ∀ first second,
        data.GroupActive first →
        data.GroupActive second →
        first ≠ second →
        data.direction first ≠ data.direction second)
    (noRight : data.hasRight = false) :
    data.IsClockwiseCompatible :=
  (isClockwiseCompatible_iff data).2
    ⟨genuine, distinct, fun hasRight => by
      rw [noRight] at hasRight
      contradiction⟩

/-- A valid ternary clause fan is supported once its literal-order
directions have the clockwise cyclic order. -/
theorem isClockwiseCompatible_of_right
    (data : ClauseRibbonFanData)
    (genuine :
      ∀ group, data.GroupActive group →
        (data.direction group).IsGenuine)
    (distinct :
      ∀ first second,
        data.GroupActive first →
        data.GroupActive second →
        first ≠ second →
        data.direction first ≠ data.direction second)
    (clockwise :
      AxisDirection.InClockwiseOrder
        (data.direction .top)
        (data.direction .left)
        (data.direction .right)) :
    data.IsClockwiseCompatible :=
  (isClockwiseCompatible_iff data).2
    ⟨genuine, distinct, fun _ => clockwise⟩

end ClauseRibbonFanData

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
