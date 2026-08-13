/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularTerminalShape

/-!
# Lane ranks for tied retained terminal gates

The finite shape records a strict radial order as a Boolean matrix.  The
annular router needs a single lane number for each gate instead.  We assign
the number of gates strictly closer to the center.

For a valid shape this rank lies in `0, …, 7`, increases along every true
radial comparison, and is injective inside each equal-direction block.
Consequently angular ties select distinct physical lanes in the same order
as their occurrence slots, without remembering any unbounded source length.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

/-- Active slots strictly closer to the center than `slot`. -/
def RetainedAngularTerminalShape.radialPredecessors
    (shape : RetainedAngularTerminalShape)
    (slot : RetainedTerminalSlot) :
    Finset RetainedTerminalSlot :=
  Finset.univ.filter fun other =>
    shape.radialLT other slot = true

/-- Zero-based radial lane number, counting gates closer to the center. -/
def RetainedAngularTerminalShape.radialRank
    (shape : RetainedAngularTerminalShape)
    (slot : RetainedTerminalSlot) : Nat :=
  (shape.radialPredecessors slot).card

/-- A valid shape has fewer than eight radial predecessors at every slot. -/
theorem RetainedAngularTerminalShape.radialRank_lt_eight
    (shape : RetainedAngularTerminalShape)
    (valid : shape.IsValid)
    (slot : RetainedTerminalSlot) :
    shape.radialRank slot < 8 := by
  have subset :
      shape.radialPredecessors slot ⊆
        (Finset.univ : Finset RetainedTerminalSlot) :=
    Finset.subset_univ _
  have slotMissing :
      slot ∉ shape.radialPredecessors slot := by
    simp [radialPredecessors,
      valid.2.2.2.1 slot]
  have strict :
      shape.radialPredecessors slot ⊂
        (Finset.univ : Finset RetainedTerminalSlot) :=
    (Finset.ssubset_iff_of_subset subset).2
      ⟨slot, Finset.mem_univ slot, slotMissing⟩
  simpa [radialRank] using
    Finset.card_lt_card strict

/-- Radial rank strictly increases along the shape's radial order. -/
theorem RetainedAngularTerminalShape.radialRank_lt_of_radialLT
    (shape : RetainedAngularTerminalShape)
    (valid : shape.IsValid)
    (first second : RetainedTerminalSlot)
    (radial : shape.radialLT first second = true) :
    shape.radialRank first < shape.radialRank second := by
  have subset :
      shape.radialPredecessors first ⊆
        shape.radialPredecessors second := by
    intro slot slotMember
    simp only [radialPredecessors,
      Finset.mem_filter, Finset.mem_univ, true_and] at slotMember ⊢
    exact valid.2.2.2.2.1
      slot first second slotMember radial
  have firstInSecond :
      first ∈ shape.radialPredecessors second := by
    simp [radialPredecessors, radial]
  have firstNotInFirst :
      first ∉ shape.radialPredecessors first := by
    simp [radialPredecessors,
      valid.2.2.2.1 first]
  have strict :
      shape.radialPredecessors first ⊂
        shape.radialPredecessors second :=
    (Finset.ssubset_iff_of_subset subset).2
      ⟨first, firstInSecond, firstNotInFirst⟩
  exact Finset.card_lt_card strict

/-- Inside one tied direction block, radial lane rank follows occurrence-slot
order. -/
theorem RetainedAngularTerminalShape.radialRank_lt_of_slot_lt
    (shape : RetainedAngularTerminalShape)
    (valid : shape.IsValid)
    (first second : RetainedTerminalSlot)
    (direction : RetainedTerminalDirection)
    (slotsLt : first.val < second.val)
    (firstDirection :
      shape.direction first = some direction)
    (secondDirection :
      shape.direction second = some direction) :
    shape.radialRank first < shape.radialRank second := by
  apply shape.radialRank_lt_of_radialLT valid
  exact valid.2.2.2.2.2.2
    first second direction slotsLt
    firstDirection secondDirection

/-- Equal-direction active slots receive different radial lanes. -/
theorem RetainedAngularTerminalShape.radialRank_injective_on_direction
    (shape : RetainedAngularTerminalShape)
    (valid : shape.IsValid)
    (first second : RetainedTerminalSlot)
    (direction : RetainedTerminalDirection)
    (firstDirection :
      shape.direction first = some direction)
    (secondDirection :
      shape.direction second = some direction)
    (ranksEqual :
      shape.radialRank first = shape.radialRank second) :
    first = second := by
  by_contra slotsNe
  rcases valid.2.2.2.2.2.1
      first second direction
      firstDirection secondDirection slotsNe with
    firstSecond | secondFirst
  · exact
      (Nat.ne_of_lt
        (shape.radialRank_lt_of_radialLT
          valid first second firstSecond))
        ranksEqual
  · exact
      (Nat.ne_of_gt
        (shape.radialRank_lt_of_radialLT
          valid second first secondFirst))
        ranksEqual

/-- A concrete valid profile can package every lane number as one of the
eight fixed lane indices. -/
def RetainedAngularTerminalProfile.radialLane
    (profile : RetainedAngularTerminalProfile)
    (distinct : profile.GatesDistinct)
    (slot : RetainedTerminalSlot) :
    RetainedTerminalSlot :=
  ⟨profile.finiteShape.radialRank slot,
    profile.finiteShape.radialRank_lt_eight
      (profile.finiteShape_isValid distinct) slot⟩

/-- Positive uniform refinement preserves every concrete radial lane. -/
theorem RetainedAngularTerminalProfile.radialLane_scale
    (profile : RetainedAngularTerminalProfile)
    (factor : Nat) (factorPositive : 0 < factor)
    (distinct : profile.GatesDistinct)
    (slot : RetainedTerminalSlot) :
    (profile.scale factor factorPositive).radialLane
        (profile.scale_gatesDistinct
          factor factorPositive distinct)
        slot =
      profile.radialLane distinct slot := by
  apply Fin.ext
  simp [radialLane, profile.finiteShape_scale
    factor factorPositive]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
