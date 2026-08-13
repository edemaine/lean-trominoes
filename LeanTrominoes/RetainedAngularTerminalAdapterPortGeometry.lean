/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularTerminalAdapterPorts
import LeanTrominoes.RetainedAngularTerminalInterfaceGeometry

/-!
# Square-frame geometry for retained terminal adapter ports

There are exactly 88 adapter-port identities.  The coordinate-radius-22
square has 176 unit boundary edges, so taking every second boundary lattice
point gives exactly 88 distinct sites.  We enumerate them clockwise, starting
at due east.

The resulting frame lies strictly outside the radius-12 Figure 7 fan and
strictly inside the radius-36 common retained-terminal interface.  Thus it is
a fixed finite seam between the unbounded inherited terminal rays and the
finite fan-routing problem.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

/-- Coordinate radius of the 88-site adapter frame. -/
def retainedTerminalAdapterFrameRadius : Nat := 22

/-- Clockwise radius-22 square coordinate of a finite adapter port, starting
at `(22, 0)` and advancing by two lattice units per port. -/
def retainedTerminalAdapterPortOffset
    (port : RetainedTerminalAdapterPort) : Cell :=
  let index : Int := port.val
  if port.val < 12 then
    (22, 2 * index)
  else if port.val < 34 then
    (44 - 2 * index, 22)
  else if port.val < 56 then
    (-22, 88 - 2 * index)
  else if port.val < 78 then
    (2 * index - 132, -22)
  else
    (22, 2 * index - 176)

/-- Every adapter port lies exactly on the coordinate-radius-22 square. -/
theorem retainedTerminalAdapterPortOffset_on_square :
    ∀ port : RetainedTerminalAdapterPort,
      WithinCoordinateRadius
          retainedTerminalAdapterFrameRadius
          (0, 0)
          (retainedTerminalAdapterPortOffset port) ∧
        ¬ WithinCoordinateRadius 21 (0, 0)
          (retainedTerminalAdapterPortOffset port) := by
  native_decide

/-- In particular, every adapter port lies strictly outside the local
radius-12 Figure 7 fan. -/
theorem retainedTerminalAdapterPortOffset_outside_fan :
    ∀ port : RetainedTerminalAdapterPort,
      ¬ WithinCoordinateRadius 12 (0, 0)
        (retainedTerminalAdapterPortOffset port) := by
  native_decide

/-- The radius-22 adapter frame is contained in the radius-36 retained-ray
interface square. -/
theorem retainedTerminalAdapterPortOffset_within_interface :
    ∀ port : RetainedTerminalAdapterPort,
      WithinCoordinateRadius 36 (0, 0)
        (retainedTerminalAdapterPortOffset port) := by
  native_decide

/-- Distinct finite port identities have distinct square-frame coordinates. -/
theorem retainedTerminalAdapterPortOffset_injective :
    Function.Injective retainedTerminalAdapterPortOffset := by
  native_decide

/-- Centering the adapter frame at an arbitrary variable preserves its exact
coordinate radius. -/
theorem retainedTerminalAdapterPortPosition_on_square
    (center : Cell)
    (port : RetainedTerminalAdapterPort) :
    WithinCoordinateRadius
        retainedTerminalAdapterFrameRadius
        center
        (Cell.add center
          (retainedTerminalAdapterPortOffset port)) ∧
      ¬ WithinCoordinateRadius 21 center
        (Cell.add center
          (retainedTerminalAdapterPortOffset port)) := by
  rcases center with ⟨centerX, centerY⟩
  simpa [WithinCoordinateRadius, Cell.add] using
    retainedTerminalAdapterPortOffset_on_square port

/-- Centered adapter positions remain strictly outside the Figure 7 fan. -/
theorem retainedTerminalAdapterPortPosition_outside_fan
    (center : Cell)
    (port : RetainedTerminalAdapterPort) :
    ¬ WithinCoordinateRadius 12 center
      (Cell.add center
        (retainedTerminalAdapterPortOffset port)) := by
  rcases center with ⟨centerX, centerY⟩
  simpa [WithinCoordinateRadius, Cell.add] using
    retainedTerminalAdapterPortOffset_outside_fan port

/-- Centered adapter positions remain inside the common radius-36 terminal
interface square. -/
theorem retainedTerminalAdapterPortPosition_within_interface
    (center : Cell)
    (port : RetainedTerminalAdapterPort) :
    WithinCoordinateRadius 36 center
      (Cell.add center
        (retainedTerminalAdapterPortOffset port)) := by
  rcases center with ⟨centerX, centerY⟩
  simpa [WithinCoordinateRadius, Cell.add] using
    retainedTerminalAdapterPortOffset_within_interface port

/-- Square-frame coordinate selected by each finite shape slot. -/
def RetainedAngularTerminalShape.adapterPortOffset
    (shape : RetainedAngularTerminalShape)
    (valid : shape.IsValid)
    (slot : RetainedTerminalSlot) :
    Option Cell :=
  (shape.adapterPort valid slot).map
    retainedTerminalAdapterPortOffset

/-- Distinct active slots of a valid shape select distinct square-frame
coordinates. -/
theorem RetainedAngularTerminalShape.adapterPortOffset_injective_on_active
    (shape : RetainedAngularTerminalShape)
    (valid : shape.IsValid)
    (first second : RetainedTerminalSlot)
    (firstDirection secondDirection :
      RetainedTerminalDirection)
    (firstDirectionEq :
      shape.direction first = some firstDirection)
    (secondDirectionEq :
      shape.direction second = some secondDirection)
    (offsetsEqual :
      shape.adapterPortOffset valid first =
        shape.adapterPortOffset valid second) :
    first = second := by
  rw [adapterPortOffset,
      shape.adapterPort_eq_some valid first
        firstDirection firstDirectionEq,
    adapterPortOffset,
      shape.adapterPort_eq_some valid second
        secondDirection secondDirectionEq] at offsetsEqual
  have portsEqual :
      retainedTerminalAdapterPort firstDirection
          ⟨shape.radialRank first,
            shape.radialRank_lt_eight valid first⟩ =
        retainedTerminalAdapterPort secondDirection
          ⟨shape.radialRank second,
            shape.radialRank_lt_eight valid second⟩ :=
    retainedTerminalAdapterPortOffset_injective
      (Option.some.inj offsetsEqual)
  exact shape.adapterPort_injective_on_active
    valid first second firstDirection secondDirection
    firstDirectionEq secondDirectionEq
    (by
      rw [shape.adapterPort_eq_some valid first
          firstDirection firstDirectionEq,
        shape.adapterPort_eq_some valid second
          secondDirection secondDirectionEq]
      exact congrArg some portsEqual)

/-- Concrete square-frame coordinate selected by each source-profile slot. -/
def RetainedAngularTerminalProfile.adapterPortOffset
    (profile : RetainedAngularTerminalProfile)
    (distinct : profile.GatesDistinct)
    (slot : RetainedTerminalSlot) :
    Option Cell :=
  (profile.adapterPort distinct slot).map
    retainedTerminalAdapterPortOffset

/-- Positive uniform refinement preserves every concrete square-frame port
coordinate. -/
theorem RetainedAngularTerminalProfile.adapterPortOffset_scale
    (profile : RetainedAngularTerminalProfile)
    (factor : Nat) (factorPositive : 0 < factor)
    (distinct : profile.GatesDistinct)
    (slot : RetainedTerminalSlot) :
    (profile.scale factor factorPositive).adapterPortOffset
        (profile.scale_gatesDistinct
          factor factorPositive distinct)
        slot =
      profile.adapterPortOffset distinct slot := by
  simp [adapterPortOffset,
    profile.adapterPort_scale factor factorPositive
      distinct slot]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
