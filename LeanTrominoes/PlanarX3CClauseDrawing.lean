/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LocalIncidenceDrawing
import LeanTrominoes.PlanarX3CClauseGadget

/-!
# Certified orthogonal drawing of the X3C clause core

The nine-set clause gadget has an eighteen-vertex outer incidence cycle.
Its left, right, and bottom internal elements form three disjoint tripods
inside that cycle.  This file gives a rectilinear realization of precisely
that embedding.

The top terminal occupies the top boundary, the left terminal the lower
boundary, and the right terminal the right boundary.  Their slot orders agree
with `X3CClauseTerminal.attachmentElement`, so the global construction can
attach the three colored occurrence strands without permutation crossings.
-/

namespace LeanTrominoes
namespace PlanarThreeDM

open Gadget

instance : Fintype X3CClauseTerminal :=
  Fintype.ofList
    [⟨.top, .first⟩, ⟨.top, .second⟩, ⟨.top, .third⟩,
      ⟨.left, .first⟩, ⟨.left, .second⟩, ⟨.left, .third⟩,
      ⟨.right, .first⟩, ⟨.right, .second⟩,
      ⟨.right, .third⟩] (by
        intro terminal
        rcases terminal with ⟨group, slot⟩
        cases group <;> cases slot <;> simp)

instance : Fintype X3CClauseElement :=
  Fintype.ofList
    [.internal .left, .internal .right, .internal .bottom,
      .terminal ⟨.top, .first⟩,
      .terminal ⟨.top, .second⟩,
      .terminal ⟨.top, .third⟩,
      .terminal ⟨.left, .first⟩,
      .terminal ⟨.left, .second⟩,
      .terminal ⟨.left, .third⟩,
      .terminal ⟨.right, .first⟩,
      .terminal ⟨.right, .second⟩,
      .terminal ⟨.right, .third⟩] (by
        intro element
        cases element with
        | internal internal => cases internal <;> simp
        | terminal terminal =>
            rcases terminal with ⟨group, slot⟩
            cases group <;> cases slot <;> simp)

namespace X3CClauseOrthogonal

/-- Rectilinear positions of the nine triple vertices. -/
def setPosition : X3CClauseSet → Cell
  | .topLeftOuter => (0, 0)
  | .topLeftInner => (8, 0)
  | .topRightInner => (16, 0)
  | .topRightOuter => (24, 0)
  | .leftMiddle => (8, 24)
  | .rightMiddle => (28, 8)
  | .bottomLeft => (16, 24)
  | .bottomRight => (28, 16)
  | .bottom => (24, 24)

/-- Rectilinear positions of the three internal and nine terminal element
vertices. -/
def elementPosition : X3CClauseElement → Cell
  | .internal .left => (4, 8)
  | .internal .right => (22, 6)
  | .internal .bottom => (22, 18)
  | .terminal ⟨.top, .first⟩ => (4, 0)
  | .terminal ⟨.top, .second⟩ => (12, 0)
  | .terminal ⟨.top, .third⟩ => (20, 0)
  | .terminal ⟨.left, .first⟩ => (4, 24)
  | .terminal ⟨.left, .second⟩ => (12, 24)
  | .terminal ⟨.left, .third⟩ => (20, 24)
  | .terminal ⟨.right, .first⟩ => (28, 4)
  | .terminal ⟨.right, .second⟩ => (28, 12)
  | .terminal ⟨.right, .third⟩ => (28, 20)

/-- The element selected by one colored reference field. -/
def reference (set : X3CClauseSet) :
    WireColor → X3CClauseElement
  | .red => set.coloredReferences.red
  | .green => set.coloredReferences.green
  | .blue => set.coloredReferences.blue

/-- Explicit orthogonal route for every colored clause-core incidence. -/
def route : X3CClauseSet → WireColor → List Cell
  | .topLeftOuter, .red =>
      [(0, 0), (0, 8), (4, 8)]
  | .topLeftOuter, .green =>
      [(0, 0), (4, 0)]
  | .topLeftOuter, .blue =>
      [(0, 0), (-4, 0), (-4, 24), (4, 24)]
  | .topLeftInner, .red =>
      [(8, 0), (8, 8), (4, 8)]
  | .topLeftInner, .green =>
      [(8, 0), (4, 0)]
  | .topLeftInner, .blue =>
      [(8, 0), (12, 0)]
  | .topRightInner, .red =>
      [(16, 0), (20, 0)]
  | .topRightInner, .green =>
      [(16, 0), (16, 6), (22, 6)]
  | .topRightInner, .blue =>
      [(16, 0), (12, 0)]
  | .topRightOuter, .red =>
      [(24, 0), (20, 0)]
  | .topRightOuter, .green =>
      [(24, 0), (24, 6), (22, 6)]
  | .topRightOuter, .blue =>
      [(24, 0), (28, 0), (28, 4)]
  | .leftMiddle, .red =>
      [(8, 24), (8, 10), (4, 10), (4, 8)]
  | .leftMiddle, .green =>
      [(8, 24), (12, 24)]
  | .leftMiddle, .blue =>
      [(8, 24), (4, 24)]
  | .rightMiddle, .red =>
      [(28, 8), (28, 12)]
  | .rightMiddle, .green =>
      [(28, 8), (22, 8), (22, 6)]
  | .rightMiddle, .blue =>
      [(28, 8), (28, 4)]
  | .bottomLeft, .red =>
      [(16, 24), (20, 24)]
  | .bottomLeft, .green =>
      [(16, 24), (12, 24)]
  | .bottomLeft, .blue =>
      [(16, 24), (16, 18), (22, 18)]
  | .bottomRight, .red =>
      [(28, 16), (28, 12)]
  | .bottomRight, .green =>
      [(28, 16), (28, 20)]
  | .bottomRight, .blue =>
      [(28, 16), (22, 16), (22, 18)]
  | .bottom, .red =>
      [(24, 24), (20, 24)]
  | .bottom, .green =>
      [(24, 24), (28, 24), (28, 20)]
  | .bottom, .blue =>
      [(24, 24), (24, 18), (22, 18)]

/-- Complete local clause-core drawing. -/
def drawing :
    LocalIncidenceDrawing X3CClauseSet X3CClauseElement where
  triplePosition := setPosition
  elementPosition := elementPosition
  reference := reference
  route := route

/-- Boundary point used by one position of the noncrossing three-strand
attachment order. -/
def attachmentPosition
    (group : X3CClauseTerminalGroup)
    (slot : X3CClauseTerminalSlot) : Cell :=
  elementPosition (.terminal (X3CClauseTerminal.attachmentElement group slot))

@[simp]
theorem top_attachmentPositions :
    [attachmentPosition .top .first,
      attachmentPosition .top .second,
      attachmentPosition .top .third] =
        [(20, 0), (12, 0), (4, 0)] := by
  rfl

@[simp]
theorem left_attachmentPositions :
    [attachmentPosition .left .first,
      attachmentPosition .left .second,
      attachmentPosition .left .third] =
        [(4, 24), (12, 24), (20, 24)] := by
  rfl

@[simp]
theorem right_attachmentPositions :
    [attachmentPosition .right .first,
      attachmentPosition .right .second,
      attachmentPosition .right .third] =
        [(28, 20), (28, 12), (28, 4)] := by
  rfl

/-- The explicit clause-core drawing has the correct endpoints, is
orthogonal, and is continuously planar. -/
theorem drawing_isValid : drawing.IsValid := by
  native_decide

end X3CClauseOrthogonal

end PlanarThreeDM
end LeanTrominoes
