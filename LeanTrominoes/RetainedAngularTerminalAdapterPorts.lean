import LeanTrominoes.RetainedAngularTerminalLaneRanks

/-!
# Finite adapter ports for retained angular terminals

The local adapter sees eleven possible retained terminal directions and at
most eight gates on any one direction.  We therefore reserve a fixed block
of eight ports for every direction, ordered first by angular rank and then
by radial lane.

This file deliberately assigns only finite port identities, not coordinates.
The subsequent geometric construction can embed these 88 identities on a
fixed outer frame while reusing the injectivity and refinement results below.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

/-- One of the `11 * 8` direction-and-lane ports available to the retained
terminal adapter. -/
abbrev RetainedTerminalAdapterPort := Fin 88

/-- The port reserved for one retained direction and one of its eight radial
lanes. -/
def retainedTerminalAdapterPort
    (direction : RetainedTerminalDirection)
    (lane : RetainedTerminalSlot) :
    RetainedTerminalAdapterPort :=
  ⟨8 * direction.angularRank + lane.val, by
    have directionLt := direction.angularRank_lt_eleven
    have laneLt := lane.isLt
    omega⟩

@[simp]
theorem retainedTerminalAdapterPort_val
    (direction : RetainedTerminalDirection)
    (lane : RetainedTerminalSlot) :
    (retainedTerminalAdapterPort direction lane).val =
      8 * direction.angularRank + lane.val :=
  rfl

/-- The finite port identity recovers both its retained direction and radial
lane. -/
theorem retainedTerminalAdapterPort_injective
    {firstDirection secondDirection :
      RetainedTerminalDirection}
    {firstLane secondLane : RetainedTerminalSlot}
    (portsEqual :
      retainedTerminalAdapterPort firstDirection firstLane =
        retainedTerminalAdapterPort secondDirection secondLane) :
    firstDirection = secondDirection ∧
      firstLane = secondLane := by
  have valuesEqual :
      8 * firstDirection.angularRank + firstLane.val =
        8 * secondDirection.angularRank + secondLane.val :=
    congrArg Fin.val portsEqual
  have firstDirectionLt :=
    firstDirection.angularRank_lt_eleven
  have secondDirectionLt :=
    secondDirection.angularRank_lt_eleven
  have firstLaneLt := firstLane.isLt
  have secondLaneLt := secondLane.isLt
  have directionsEqual :
      firstDirection.angularRank =
        secondDirection.angularRank := by
    omega
  have lanesEqual : firstLane.val = secondLane.val := by
    omega
  exact
    ⟨RetainedTerminalDirection.angularRank_injective
        directionsEqual,
      Fin.ext lanesEqual⟩

/-- Port selected by a finite shape slot.  Inactive slots select no port. -/
def RetainedAngularTerminalShape.adapterPort
    (shape : RetainedAngularTerminalShape)
    (valid : shape.IsValid)
    (slot : RetainedTerminalSlot) :
    Option RetainedTerminalAdapterPort :=
  (shape.direction slot).map fun direction =>
    retainedTerminalAdapterPort direction
      ⟨shape.radialRank slot,
        shape.radialRank_lt_eight valid slot⟩

/-- An active shape slot selects the port formed from its exact direction and
radial rank. -/
theorem RetainedAngularTerminalShape.adapterPort_eq_some
    (shape : RetainedAngularTerminalShape)
    (valid : shape.IsValid)
    (slot : RetainedTerminalSlot)
    (direction : RetainedTerminalDirection)
    (directionEq :
      shape.direction slot = some direction) :
    shape.adapterPort valid slot =
      some
        (retainedTerminalAdapterPort direction
          ⟨shape.radialRank slot,
            shape.radialRank_lt_eight valid slot⟩) := by
  simp [adapterPort, directionEq]

/-- Inactive shape slots select no adapter port. -/
theorem RetainedAngularTerminalShape.adapterPort_eq_none
    (shape : RetainedAngularTerminalShape)
    (valid : shape.IsValid)
    (slot : RetainedTerminalSlot)
    (directionEq : shape.direction slot = none) :
    shape.adapterPort valid slot = none := by
  simp [adapterPort, directionEq]

/-- Distinct active slots of a valid shape select distinct adapter ports.
Different directions occupy different blocks; tied directions are separated
by the injective radial lane rank. -/
theorem RetainedAngularTerminalShape.adapterPort_injective_on_active
    (shape : RetainedAngularTerminalShape)
    (valid : shape.IsValid)
    (first second : RetainedTerminalSlot)
    (firstDirection secondDirection :
      RetainedTerminalDirection)
    (firstDirectionEq :
      shape.direction first = some firstDirection)
    (secondDirectionEq :
      shape.direction second = some secondDirection)
    (portsEqual :
      shape.adapterPort valid first =
        shape.adapterPort valid second) :
    first = second := by
  rw [shape.adapterPort_eq_some valid first
      firstDirection firstDirectionEq,
    shape.adapterPort_eq_some valid second
      secondDirection secondDirectionEq] at portsEqual
  have componentsEqual :=
    retainedTerminalAdapterPort_injective
      (Option.some.inj portsEqual)
  have directionsEqual :
      firstDirection = secondDirection :=
    componentsEqual.1
  have ranksEqual :
      shape.radialRank first =
        shape.radialRank second :=
    congrArg Fin.val componentsEqual.2
  exact shape.radialRank_injective_on_direction
    valid first second firstDirection
    firstDirectionEq
    (directionsEqual ▸ secondDirectionEq)
    ranksEqual

/-- The concrete port selected by every source-profile slot. -/
def RetainedAngularTerminalProfile.adapterPort
    (profile : RetainedAngularTerminalProfile)
    (distinct : profile.GatesDistinct)
    (slot : RetainedTerminalSlot) :
    Option RetainedTerminalAdapterPort :=
  profile.finiteShape.adapterPort
    (profile.finiteShape_isValid distinct) slot

/-- Positive uniform refinement preserves every concrete adapter port. -/
theorem RetainedAngularTerminalProfile.adapterPort_scale
    (profile : RetainedAngularTerminalProfile)
    (factor : Nat) (factorPositive : 0 < factor)
    (distinct : profile.GatesDistinct)
    (slot : RetainedTerminalSlot) :
    (profile.scale factor factorPositive).adapterPort
        (profile.scale_gatesDistinct
          factor factorPositive distinct)
        slot =
      profile.adapterPort distinct slot := by
  simp [adapterPort,
    RetainedAngularTerminalShape.adapterPort,
    profile.finiteShape_scale factor factorPositive]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
