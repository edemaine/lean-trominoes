import LeanTrominoes.RetainedAngularFanAnchorRoutes

/-!
# Order-compatible demands across the retained fan annulus

The finite fan-side router must join a shape-dependent radius-33 fan-facing
port to the radius-22 compass anchor of the same occurrence slot.  This file
packages those two endpoints as one optional demand per slot.

For every valid shape, active demands have injective outer and inner
endpoints.  More importantly, their outer port order is equivalent to their
inner anchor order, both of which are exactly occurrence-slot order.  This is
the order-compatibility premise needed by a noncrossing annular router.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

/-- One active connection requested across the fan-side annulus. -/
@[ext]
structure RetainedAngularFanAnnulusDemand where
  outer : Cell
  inner : Cell
  deriving DecidableEq, Repr

/-- Optional annular demand selected by one finite shape slot. -/
def RetainedAngularTerminalShape.fanAnnulusDemand
    (shape : RetainedAngularTerminalShape)
    (slot : RetainedTerminalSlot) :
    Option RetainedAngularFanAnnulusDemand :=
  (shape.fanPortOffset slot).map fun outer =>
    { outer := outer
      inner :=
        retainedTerminalAdapterPortOffset
          (retainedTerminalFanAnchorPort slot) }

/-- Exact demand selected by an active shape slot. -/
theorem RetainedAngularTerminalShape.fanAnnulusDemand_eq_some
    (shape : RetainedAngularTerminalShape)
    (slot : RetainedTerminalSlot)
    (direction : RetainedTerminalDirection)
    (directionEq :
      shape.direction slot = some direction) :
    shape.fanAnnulusDemand slot =
      some
        { outer :=
            retainedTerminalFanPortOffset
              (retainedTerminalFanPort direction slot)
          inner :=
            retainedTerminalAdapterPortOffset
              (retainedTerminalFanAnchorPort slot) } := by
  simp [fanAnnulusDemand,
    RetainedAngularTerminalShape.fanPortOffset,
    shape.fanPort_eq_some slot direction directionEq]

/-- Inactive shape slots request no annular connection. -/
theorem RetainedAngularTerminalShape.fanAnnulusDemand_eq_none
    (shape : RetainedAngularTerminalShape)
    (slot : RetainedTerminalSlot)
    (directionEq : shape.direction slot = none) :
    shape.fanAnnulusDemand slot = none := by
  simp [fanAnnulusDemand,
    RetainedAngularTerminalShape.fanPortOffset,
    RetainedAngularTerminalShape.fanPort,
    directionEq]

/-- For active slots, fan-facing port order is exactly occurrence-slot order. -/
theorem RetainedAngularTerminalShape.fanPort_val_lt_iff_slot_lt
    (shape : RetainedAngularTerminalShape)
    (valid : shape.IsValid)
    (first second : RetainedTerminalSlot)
    (firstDirection secondDirection :
      RetainedTerminalDirection)
    (firstDirectionEq :
      shape.direction first = some firstDirection)
    (secondDirectionEq :
      shape.direction second = some secondDirection) :
    (retainedTerminalFanPort firstDirection first).val <
        (retainedTerminalFanPort secondDirection second).val ↔
      first.val < second.val := by
  constructor
  · intro portsLt
    by_contra slotsNotLt
    have slotsLe : second.val ≤ first.val :=
      Nat.le_of_not_gt slotsNotLt
    rcases Nat.eq_or_lt_of_le slotsLe with
      slotsEq | slotsLt
    · have slotsEqual : first = second :=
        Fin.ext slotsEq.symm
      subst second
      have directionsEqual :
          secondDirection = firstDirection := by
        rw [firstDirectionEq] at secondDirectionEq
        exact (Option.some.inj secondDirectionEq).symm
      subst secondDirection
      exact (Nat.lt_irrefl _ portsLt)
    · have reverseLt :=
        shape.fanPort_val_lt valid
          second first secondDirection firstDirection
          slotsLt secondDirectionEq firstDirectionEq
      omega
  · intro slotsLt
    exact shape.fanPort_val_lt valid
      first second firstDirection secondDirection
      slotsLt firstDirectionEq secondDirectionEq

/-- Compass-anchor port order is exactly occurrence-slot order. -/
theorem retainedTerminalFanAnchorPort_val_lt_iff
    (first second : RetainedTerminalSlot) :
    (retainedTerminalFanAnchorPort first).val <
        (retainedTerminalFanAnchorPort second).val ↔
      first.val < second.val := by
  simp only [retainedTerminalFanAnchorPort_val]
  omega

/-- Active outer fan-facing ports and inner compass anchors induce the same
strict clockwise order. -/
theorem RetainedAngularTerminalShape.fanAnnulus_port_order_compatible
    (shape : RetainedAngularTerminalShape)
    (valid : shape.IsValid)
    (first second : RetainedTerminalSlot)
    (firstDirection secondDirection :
      RetainedTerminalDirection)
    (firstDirectionEq :
      shape.direction first = some firstDirection)
    (secondDirectionEq :
      shape.direction second = some secondDirection) :
    (retainedTerminalFanPort firstDirection first).val <
        (retainedTerminalFanPort secondDirection second).val ↔
      (retainedTerminalFanAnchorPort first).val <
        (retainedTerminalFanAnchorPort second).val := by
  rw [shape.fanPort_val_lt_iff_slot_lt valid
      first second firstDirection secondDirection
      firstDirectionEq secondDirectionEq,
    retainedTerminalFanAnchorPort_val_lt_iff]

/-- Direction-and-slot fan ports have pairwise distinct outer endpoints. -/
theorem retainedTerminalFanPortOffset_injective_slots
    (first second : RetainedTerminalSlot)
    (firstDirection secondDirection :
      RetainedTerminalDirection)
    (outerEqual :
      (retainedTerminalFanPortOffset
          (retainedTerminalFanPort firstDirection first)) =
        retainedTerminalFanPortOffset
          (retainedTerminalFanPort secondDirection second)) :
    first = second := by
  have portsEqual :=
    retainedTerminalFanPortOffset_injective outerEqual
  exact
    (retainedTerminalFanPort_injective portsEqual).2

/-- Inner compass-anchor endpoints are injective in the occurrence slot. -/
theorem retainedTerminalFanAnchorPortOffset_injective :
    Function.Injective fun slot : RetainedTerminalSlot =>
      retainedTerminalAdapterPortOffset
        (retainedTerminalFanAnchorPort slot) := by
  intro first second offsetsEqual
  exact retainedTerminalFanAnchorPort_injective
    (retainedTerminalAdapterPortOffset_injective offsetsEqual)

/-- Distinct active slots request distinct full annular demands. -/
theorem RetainedAngularTerminalShape.fanAnnulusDemand_injective_on_active
    (shape : RetainedAngularTerminalShape)
    (first second : RetainedTerminalSlot)
    (firstDirection secondDirection :
      RetainedTerminalDirection)
    (firstDirectionEq :
      shape.direction first = some firstDirection)
    (secondDirectionEq :
      shape.direction second = some secondDirection)
    (demandsEqual :
      shape.fanAnnulusDemand first =
        shape.fanAnnulusDemand second) :
    first = second := by
  rw [shape.fanAnnulusDemand_eq_some first
      firstDirection firstDirectionEq,
    shape.fanAnnulusDemand_eq_some second
      secondDirection secondDirectionEq] at demandsEqual
  have outerEqual :
      retainedTerminalFanPortOffset
          (retainedTerminalFanPort firstDirection first) =
        retainedTerminalFanPortOffset
          (retainedTerminalFanPort secondDirection second) :=
    congrArg RetainedAngularFanAnnulusDemand.outer
      (Option.some.inj demandsEqual)
  exact retainedTerminalFanPortOffset_injective_slots
    first second firstDirection secondDirection
    outerEqual

/-- Concrete annular demand selected by a source-profile slot. -/
def RetainedAngularTerminalProfile.fanAnnulusDemand
    (profile : RetainedAngularTerminalProfile)
    (slot : RetainedTerminalSlot) :
    Option RetainedAngularFanAnnulusDemand :=
  profile.finiteShape.fanAnnulusDemand slot

/-- Positive uniform refinement preserves every concrete fan-annulus demand. -/
theorem RetainedAngularTerminalProfile.fanAnnulusDemand_scale
    (profile : RetainedAngularTerminalProfile)
    (factor : Nat) (factorPositive : 0 < factor)
    (slot : RetainedTerminalSlot) :
    (profile.scale factor factorPositive).fanAnnulusDemand slot =
      profile.fanAnnulusDemand slot := by
  simp [fanAnnulusDemand,
    RetainedAngularTerminalShape.fanAnnulusDemand,
    RetainedAngularTerminalShape.fanPortOffset,
    RetainedAngularTerminalShape.fanPort,
    profile.finiteShape_scale factor factorPositive]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
