import LeanTrominoes.RetainedAngularTerminalGateDistinctness
import LeanTrominoes.RetainedTerminalDirectionEnumeration
import Mathlib.Data.Fintype.Pi

/-!
# Finite shapes of retained angular terminal profiles

Concrete retained terminal lengths are unbounded, but an annular adapter
only needs three finite facts about them:

* which of the eight Figure 7 slots are active;
* the retained direction at each active slot; and
* for two gates on the same ray, which one is radially closer.

`RetainedAngularTerminalShape` records exactly that information in eight
fixed slots.  It is a finite type, so later executable geometry can search
all possible local inputs.  The extraction theorems below recover the exact
direction and strict radial comparison of every active pair, and show that
positive uniform refinement leaves the shape unchanged.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

/-- One of the eight consecutive boundary slots in the Figure 7 fan. -/
abbrev RetainedTerminalSlot := Fin 8

/-- Finite data controlling one local annular adapter.

Inactive slots contain `none`.  `radialLT first second` is meaningful for
active slots of equal direction and says that the first gate is closer to
the variable center than the second. -/
@[ext]
structure RetainedAngularTerminalShape where
  direction :
    RetainedTerminalSlot →
      Option RetainedTerminalDirection
  radialLT :
    RetainedTerminalSlot →
      RetainedTerminalSlot → Bool
  deriving DecidableEq, Fintype

/-- Extract the bounded adapter shape from a concrete length-aware profile. -/
def RetainedAngularTerminalProfile.finiteShape
    (profile : RetainedAngularTerminalProfile) :
    RetainedAngularTerminalShape where
  direction := fun slot =>
    (profile.terminals[slot.val]?).map Prod.fst
  radialLT := fun first second =>
    match profile.terminals[first.val]?,
        profile.terminals[second.val]? with
    | some firstTerminal, some secondTerminal =>
        decide
          (firstTerminal.1 = secondTerminal.1 ∧
            firstTerminal.2 < secondTerminal.2)
    | _, _ => false

/-- An active slot exposes exactly the concrete terminal direction at that
list index. -/
theorem RetainedAngularTerminalProfile.finiteShape_direction_of_lt
    (profile : RetainedAngularTerminalProfile)
    (slot : RetainedTerminalSlot)
    (slotLt : slot.val < profile.terminals.length) :
    profile.finiteShape.direction slot =
      some (profile.terminals[slot.val]'slotLt).1 := by
  simp [finiteShape, List.getElem?_eq_getElem slotLt]

/-- A slot beyond the concrete terminal list is inactive. -/
theorem RetainedAngularTerminalProfile.finiteShape_direction_of_ge
    (profile : RetainedAngularTerminalProfile)
    (slot : RetainedTerminalSlot)
    (slotGe : profile.terminals.length ≤ slot.val) :
    profile.finiteShape.direction slot = none := by
  simp [finiteShape,
    List.getElem?_eq_none_iff.mpr slotGe]

/-- On active slots, the finite radial bit is precisely strict comparison of
the concrete lengths, restricted to a common retained direction. -/
theorem RetainedAngularTerminalProfile.finiteShape_radialLT_of_lt
    (profile : RetainedAngularTerminalProfile)
    (first second : RetainedTerminalSlot)
    (firstLt : first.val < profile.terminals.length)
    (secondLt : second.val < profile.terminals.length) :
    profile.finiteShape.radialLT first second =
      decide
        ((profile.terminals[first.val]'firstLt).1 =
            (profile.terminals[second.val]'secondLt).1 ∧
          (profile.terminals[first.val]'firstLt).2 <
            (profile.terminals[second.val]'secondLt).2) := by
  simp [finiteShape,
    List.getElem?_eq_getElem firstLt,
    List.getElem?_eq_getElem secondLt]

/-- Positive uniform refinement changes physical radii but not the finite
adapter shape. -/
theorem RetainedAngularTerminalProfile.finiteShape_scale
    (profile : RetainedAngularTerminalProfile)
    (factor : Nat) (factorPositive : 0 < factor) :
    (profile.scale factor factorPositive).finiteShape =
      profile.finiteShape := by
  apply RetainedAngularTerminalShape.ext
  · funext slot
    cases slotLookup :
        profile.terminals[slot.val]? with
    | none =>
        simp [finiteShape,
          RetainedAngularTerminalProfile.scale,
          slotLookup]
    | some terminal =>
        simp [finiteShape,
          RetainedAngularTerminalProfile.scale,
          slotLookup, scaleRetainedTerminalData]
  · funext first second
    cases firstLookup :
        profile.terminals[first.val]? with
    | none =>
        simp [finiteShape,
          RetainedAngularTerminalProfile.scale,
          firstLookup]
    | some firstTerminal =>
        cases secondLookup :
            profile.terminals[second.val]? with
        | none =>
            simp [finiteShape,
              RetainedAngularTerminalProfile.scale,
              firstLookup, secondLookup]
        | some secondTerminal =>
            simp [finiteShape,
              RetainedAngularTerminalProfile.scale,
              firstLookup, secondLookup,
              scaleRetainedTerminalData,
              Nat.mul_lt_mul_left factorPositive]

/-- Distinct active gates on one ray have a strict radial order in one of
the two directions. -/
theorem RetainedAngularTerminalProfile.finiteShape_radialLT_total
    (profile : RetainedAngularTerminalProfile)
    (distinct : profile.GatesDistinct)
    (first second : RetainedTerminalSlot)
    (firstLt : first.val < profile.terminals.length)
    (secondLt : second.val < profile.terminals.length)
    (slotsNe : first ≠ second)
    (directionsEqual :
      (profile.terminals[first.val]'firstLt).1 =
        (profile.terminals[second.val]'secondLt).1) :
    profile.finiteShape.radialLT first second = true ∨
      profile.finiteShape.radialLT second first = true := by
  have terminalsNe :
      profile.terminals[first.val]'firstLt ≠
        profile.terminals[second.val]'secondLt := by
    intro terminalsEqual
    have indicesEqual :
        (⟨first.val, firstLt⟩ :
            Fin profile.terminals.length) =
          ⟨second.val, secondLt⟩ :=
      (List.nodup_iff_injective_getElem.mp distinct)
        terminalsEqual
    apply slotsNe
    have valuesEqual : first.val = second.val :=
      congrArg
        (fun index : Fin profile.terminals.length =>
          index.val)
        indicesEqual
    exact Fin.ext valuesEqual
  have lengthsNe :
      (profile.terminals[first.val]'firstLt).2 ≠
        (profile.terminals[second.val]'secondLt).2 := by
    intro lengthsEqual
    apply terminalsNe
    exact Prod.ext directionsEqual lengthsEqual
  rw [profile.finiteShape_radialLT_of_lt
      first second firstLt secondLt,
    profile.finiteShape_radialLT_of_lt
      second first secondLt firstLt]
  simp only [decide_eq_true_eq, directionsEqual,
    true_and]
  exact Nat.lt_or_gt_of_ne lengthsNe

end PeriodicEightOccurrenceSplit
end LeanTrominoes
