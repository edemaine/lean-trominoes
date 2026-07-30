import LeanTrominoes.RetainedAngularTerminalAdapterPortGeometry

/-!
# Fan-facing ports for retained angular terminals

Radial lane rank separates gates that lie on the same retained ray, but those
lanes need not occur in the same order as the source formula's stable angular
occurrence list.  The Figure 7 boundary must use the latter order.

We therefore define a second use of the same 88-site square frame.  A
fan-facing port is indexed by retained direction and by the occurrence slot
itself.  Valid shapes have nondecreasing direction ranks, so active
fan-facing ports advance strictly clockwise with occurrence-slot order.
Together with the radial adapter ports, these sites expose the finite
within-direction permutation that the local router must realize.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

/-- Fan-facing square port for a retained direction and its occurrence slot. -/
def retainedTerminalFanPort
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) :
    RetainedTerminalAdapterPort :=
  ⟨8 * direction.angularRank + slot.val, by
    have directionLt := direction.angularRank_lt_eleven
    have slotLt := slot.isLt
    omega⟩

@[simp]
theorem retainedTerminalFanPort_val
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) :
    (retainedTerminalFanPort direction slot).val =
      8 * direction.angularRank + slot.val :=
  rfl

/-- A fan-facing port recovers both its direction and occurrence slot. -/
theorem retainedTerminalFanPort_injective
    {firstDirection secondDirection :
      RetainedTerminalDirection}
    {firstSlot secondSlot : RetainedTerminalSlot}
    (portsEqual :
      retainedTerminalFanPort firstDirection firstSlot =
        retainedTerminalFanPort secondDirection secondSlot) :
    firstDirection = secondDirection ∧
      firstSlot = secondSlot := by
  have valuesEqual :
      8 * firstDirection.angularRank + firstSlot.val =
        8 * secondDirection.angularRank + secondSlot.val :=
    congrArg Fin.val portsEqual
  have firstDirectionLt :=
    firstDirection.angularRank_lt_eleven
  have secondDirectionLt :=
    secondDirection.angularRank_lt_eleven
  have firstSlotLt := firstSlot.isLt
  have secondSlotLt := secondSlot.isLt
  have directionsEqual :
      firstDirection.angularRank =
        secondDirection.angularRank := by
    omega
  have slotsEqual : firstSlot.val = secondSlot.val := by
    omega
  exact
    ⟨RetainedTerminalDirection.angularRank_injective
        directionsEqual,
      Fin.ext slotsEqual⟩

/-- Fan-facing port selected by a shape slot.  Inactive slots select none. -/
def RetainedAngularTerminalShape.fanPort
    (shape : RetainedAngularTerminalShape)
    (slot : RetainedTerminalSlot) :
    Option RetainedTerminalAdapterPort :=
  (shape.direction slot).map fun direction =>
    retainedTerminalFanPort direction slot

/-- Exact fan-facing port selected by an active shape slot. -/
theorem RetainedAngularTerminalShape.fanPort_eq_some
    (shape : RetainedAngularTerminalShape)
    (slot : RetainedTerminalSlot)
    (direction : RetainedTerminalDirection)
    (directionEq :
      shape.direction slot = some direction) :
    shape.fanPort slot =
      some (retainedTerminalFanPort direction slot) := by
  simp [fanPort, directionEq]

/-- Earlier active slots of a valid shape select strictly earlier clockwise
fan-facing ports. -/
theorem RetainedAngularTerminalShape.fanPort_val_lt
    (shape : RetainedAngularTerminalShape)
    (valid : shape.IsValid)
    (first second : RetainedTerminalSlot)
    (firstDirection secondDirection :
      RetainedTerminalDirection)
    (slotsLt : first.val < second.val)
    (firstDirectionEq :
      shape.direction first = some firstDirection)
    (secondDirectionEq :
      shape.direction second = some secondDirection) :
    (retainedTerminalFanPort firstDirection first).val <
      (retainedTerminalFanPort secondDirection second).val := by
  have ranksLe :
      firstDirection.angularRank ≤
        secondDirection.angularRank :=
    valid.2.1 first second
      firstDirection secondDirection slotsLt
      firstDirectionEq secondDirectionEq
  simp only [retainedTerminalFanPort_val]
  have firstSlotLt := first.isLt
  have secondSlotLt := second.isLt
  omega

/-- Distinct active slots select distinct fan-facing ports. -/
theorem RetainedAngularTerminalShape.fanPort_injective_on_active
    (shape : RetainedAngularTerminalShape)
    (first second : RetainedTerminalSlot)
    (firstDirection secondDirection :
      RetainedTerminalDirection)
    (firstDirectionEq :
      shape.direction first = some firstDirection)
    (secondDirectionEq :
      shape.direction second = some secondDirection)
    (portsEqual :
      shape.fanPort first = shape.fanPort second) :
    first = second := by
  rw [shape.fanPort_eq_some first
      firstDirection firstDirectionEq,
    shape.fanPort_eq_some second
      secondDirection secondDirectionEq] at portsEqual
  exact
    (retainedTerminalFanPort_injective
      (Option.some.inj portsEqual)).2

/-- Square-frame coordinate of a shape's fan-facing port. -/
def RetainedAngularTerminalShape.fanPortOffset
    (shape : RetainedAngularTerminalShape)
    (slot : RetainedTerminalSlot) :
    Option Cell :=
  (shape.fanPort slot).map
    retainedTerminalAdapterPortOffset

/-- Distinct active slots select distinct fan-facing frame coordinates. -/
theorem RetainedAngularTerminalShape.fanPortOffset_injective_on_active
    (shape : RetainedAngularTerminalShape)
    (first second : RetainedTerminalSlot)
    (firstDirection secondDirection :
      RetainedTerminalDirection)
    (firstDirectionEq :
      shape.direction first = some firstDirection)
    (secondDirectionEq :
      shape.direction second = some secondDirection)
    (offsetsEqual :
      shape.fanPortOffset first =
        shape.fanPortOffset second) :
    first = second := by
  rw [fanPortOffset,
      shape.fanPort_eq_some first
        firstDirection firstDirectionEq,
    fanPortOffset,
      shape.fanPort_eq_some second
        secondDirection secondDirectionEq] at offsetsEqual
  have portsEqual :=
    retainedTerminalAdapterPortOffset_injective
      (Option.some.inj offsetsEqual)
  exact
    (retainedTerminalFanPort_injective portsEqual).2

/-- Concrete fan-facing port selected by a source-profile slot. -/
def RetainedAngularTerminalProfile.fanPort
    (profile : RetainedAngularTerminalProfile)
    (slot : RetainedTerminalSlot) :
    Option RetainedTerminalAdapterPort :=
  profile.finiteShape.fanPort slot

/-- Positive uniform refinement preserves every concrete fan-facing port. -/
theorem RetainedAngularTerminalProfile.fanPort_scale
    (profile : RetainedAngularTerminalProfile)
    (factor : Nat) (factorPositive : 0 < factor)
    (slot : RetainedTerminalSlot) :
    (profile.scale factor factorPositive).fanPort slot =
      profile.fanPort slot := by
  simp [fanPort, RetainedAngularTerminalShape.fanPort,
    profile.finiteShape_scale factor factorPositive]

/-- Concrete square coordinate selected by a source-profile slot on the
fan-facing frame. -/
def RetainedAngularTerminalProfile.fanPortOffset
    (profile : RetainedAngularTerminalProfile)
    (slot : RetainedTerminalSlot) :
    Option Cell :=
  (profile.fanPort slot).map
    retainedTerminalAdapterPortOffset

/-- Positive uniform refinement preserves every concrete fan-facing square
coordinate. -/
theorem RetainedAngularTerminalProfile.fanPortOffset_scale
    (profile : RetainedAngularTerminalProfile)
    (factor : Nat) (factorPositive : 0 < factor)
    (slot : RetainedTerminalSlot) :
    (profile.scale factor factorPositive).fanPortOffset slot =
      profile.fanPortOffset slot := by
  simp [fanPortOffset,
    profile.fanPort_scale factor factorPositive slot]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
