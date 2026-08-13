/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PlanarX3CClauseGadget

/-!
# The fixed-red Dyer--Frieze connector

The ordinary variable-cycle occurrence gadget has a three-element terminal
whose red and green elements may be exchanged, but whose blue element has a
fixed position.  Figure 6 of Dyer and Frieze gives a planar detour that can
instead put the fixed element in the red position.  (Their yellow color is
called green throughout this development.)

This file transcribes that detour as a two-by-three ladder plus one auxiliary
triple.  The eight internal colored elements all have degree two.  Covering
them exactly once leaves precisely two alternating selections.  At either
selection, the three connector ports are all covered or all uncovered, while
the two ports continuing the variable cycle have opposite states.
-/

namespace LeanTrominoes
namespace PlanarThreeDM

/-- The six ladder triples and the terminal-producing auxiliary triple. -/
inductive FixedRedConnectorTriple
  | topLeft
  | topMiddle
  | topRight
  | bottomLeft
  | bottomMiddle
  | bottomRight
  | auxiliary
  deriving DecidableEq, Repr, Fintype

/-- Red elements of the fixed-red connector. -/
inductive FixedRedConnectorRed
  | leftTopPort
  | leftBottomPort
  | middleRung
  | topAuxiliary
  | connectorPort
  deriving DecidableEq, Repr, Fintype

/-- Green elements of the fixed-red connector. -/
inductive FixedRedConnectorGreen
  | leftRung
  | topRightLink
  | bottomRightLink
  | connectorPort
  deriving DecidableEq, Repr, Fintype

/-- Blue elements of the fixed-red connector. -/
inductive FixedRedConnectorBlue
  | topLeftLink
  | bottomLeftLink
  | rightRung
  | connectorPort
  deriving DecidableEq, Repr, Fintype

/-- One red, green, and blue reference for each connector triple. -/
structure FixedRedConnectorReferences where
  red : FixedRedConnectorRed
  green : FixedRedConnectorGreen
  blue : FixedRedConnectorBlue
  deriving DecidableEq, Repr

namespace FixedRedConnectorTriple

/-- The colored element references in Figure 6. -/
def references : FixedRedConnectorTriple → FixedRedConnectorReferences
  | .topLeft =>
      ⟨.leftTopPort, .leftRung, .topLeftLink⟩
  | .topMiddle =>
      ⟨.middleRung, .topRightLink, .topLeftLink⟩
  | .topRight =>
      ⟨.topAuxiliary, .topRightLink, .rightRung⟩
  | .bottomLeft =>
      ⟨.leftBottomPort, .leftRung, .bottomLeftLink⟩
  | .bottomMiddle =>
      ⟨.middleRung, .bottomRightLink, .bottomLeftLink⟩
  | .bottomRight =>
      ⟨.connectorPort, .bottomRightLink, .rightRung⟩
  | .auxiliary =>
      ⟨.topAuxiliary, .connectorPort, .connectorPort⟩

/-- Integer coordinates for the planar ladder layout. -/
def position : FixedRedConnectorTriple → Cell
  | .topLeft => (0, 0)
  | .topMiddle => (4, 0)
  | .topRight => (8, 0)
  | .bottomLeft => (0, 4)
  | .bottomMiddle => (4, 4)
  | .bottomRight => (8, 4)
  | .auxiliary => (12, 0)

end FixedRedConnectorTriple

namespace FixedRedConnectorRed

/-- Triples incident to each red element.  The three port cases have one
local incidence; the two internal cases have two. -/
def neighbors : FixedRedConnectorRed → List FixedRedConnectorTriple
  | .leftTopPort => [.topLeft]
  | .leftBottomPort => [.bottomLeft]
  | .middleRung => [.topMiddle, .bottomMiddle]
  | .topAuxiliary => [.topRight, .auxiliary]
  | .connectorPort => [.bottomRight]

/-- Integer coordinates for the red elements. -/
def position : FixedRedConnectorRed → Cell
  | .leftTopPort => (-2, 0)
  | .leftBottomPort => (-2, 4)
  | .middleRung => (4, 2)
  | .topAuxiliary => (10, 0)
  | .connectorPort => (10, 4)

end FixedRedConnectorRed

namespace FixedRedConnectorGreen

/-- Triples incident to each green element. -/
def neighbors : FixedRedConnectorGreen → List FixedRedConnectorTriple
  | .leftRung => [.topLeft, .bottomLeft]
  | .topRightLink => [.topMiddle, .topRight]
  | .bottomRightLink => [.bottomMiddle, .bottomRight]
  | .connectorPort => [.auxiliary]

/-- Integer coordinates for the green elements. -/
def position : FixedRedConnectorGreen → Cell
  | .leftRung => (0, 2)
  | .topRightLink => (6, 0)
  | .bottomRightLink => (6, 4)
  | .connectorPort => (14, -1)

end FixedRedConnectorGreen

namespace FixedRedConnectorBlue

/-- Triples incident to each blue element. -/
def neighbors : FixedRedConnectorBlue → List FixedRedConnectorTriple
  | .topLeftLink => [.topLeft, .topMiddle]
  | .bottomLeftLink => [.bottomLeft, .bottomMiddle]
  | .rightRung => [.topRight, .bottomRight]
  | .connectorPort => [.auxiliary]

/-- Integer coordinates for the blue elements. -/
def position : FixedRedConnectorBlue → Cell
  | .topLeftLink => (2, 0)
  | .bottomLeftLink => (2, 4)
  | .rightRung => (8, 2)
  | .connectorPort => (14, 1)

end FixedRedConnectorBlue

/-- The red incidence list agrees with the triple references. -/
theorem fixedRedConnector_mem_red_neighbors_iff
    (triple : FixedRedConnectorTriple)
    (element : FixedRedConnectorRed) :
    triple ∈ element.neighbors ↔ triple.references.red = element := by
  cases triple <;> cases element <;> native_decide

/-- The green incidence list agrees with the triple references. -/
theorem fixedRedConnector_mem_green_neighbors_iff
    (triple : FixedRedConnectorTriple)
    (element : FixedRedConnectorGreen) :
    triple ∈ element.neighbors ↔ triple.references.green = element := by
  cases triple <;> cases element <;> native_decide

/-- The blue incidence list agrees with the triple references. -/
theorem fixedRedConnector_mem_blue_neighbors_iff
    (triple : FixedRedConnectorTriple)
    (element : FixedRedConnectorBlue) :
    triple ∈ element.neighbors ↔ triple.references.blue = element := by
  cases triple <;> cases element <;> native_decide

/-- Exact-cover constraints on the eight internal elements.  The five ports
are deliberately omitted because the surrounding variable cycle and clause
terminal provide their remaining incidences. -/
def FixedRedConnectorHolds
    (selected : FixedRedConnectorTriple → Bool) : Prop :=
  PeriodicOneInThree.ExactlyOne
      ((FixedRedConnectorRed.neighbors .middleRung).map selected) ∧
    PeriodicOneInThree.ExactlyOne
      ((FixedRedConnectorRed.neighbors .topAuxiliary).map selected) ∧
    PeriodicOneInThree.ExactlyOne
      ((FixedRedConnectorGreen.neighbors .leftRung).map selected) ∧
    PeriodicOneInThree.ExactlyOne
      ((FixedRedConnectorGreen.neighbors .topRightLink).map selected) ∧
    PeriodicOneInThree.ExactlyOne
      ((FixedRedConnectorGreen.neighbors .bottomRightLink).map selected) ∧
    PeriodicOneInThree.ExactlyOne
      ((FixedRedConnectorBlue.neighbors .topLeftLink).map selected) ∧
    PeriodicOneInThree.ExactlyOne
      ((FixedRedConnectorBlue.neighbors .bottomLeftLink).map selected) ∧
    PeriodicOneInThree.ExactlyOne
      ((FixedRedConnectorBlue.neighbors .rightRung).map selected)

instance (selected : FixedRedConnectorTriple → Bool) :
    Decidable (FixedRedConnectorHolds selected) := by
  unfold FixedRedConnectorHolds
  infer_instance

/-- The alternating ladder selection determined by its top-left state. -/
def fixedRedConnectorSelection
    (value : Bool) : FixedRedConnectorTriple → Bool
  | .topLeft => value
  | .topMiddle => !value
  | .topRight => value
  | .bottomLeft => !value
  | .bottomMiddle => value
  | .bottomRight => !value
  | .auxiliary => !value

/-- Write seven Boolean values as a connector selection. -/
private def fixedRedConnectorAssignment
    (topLeft topMiddle topRight bottomLeft bottomMiddle bottomRight
      auxiliary : Bool) :
    FixedRedConnectorTriple → Bool
  | .topLeft => topLeft
  | .topMiddle => topMiddle
  | .topRight => topRight
  | .bottomLeft => bottomLeft
  | .bottomMiddle => bottomMiddle
  | .bottomRight => bottomRight
  | .auxiliary => auxiliary

/-- Exhaustive seven-bit truth table for the connector. -/
private theorem fixedRedConnectorAssignment_holds_iff
    (topLeft topMiddle topRight bottomLeft bottomMiddle bottomRight
      auxiliary : Bool) :
    FixedRedConnectorHolds
        (fixedRedConnectorAssignment topLeft topMiddle topRight bottomLeft
          bottomMiddle bottomRight auxiliary) ↔
      (topLeft = true ∧ topMiddle = false ∧ topRight = true ∧
          bottomLeft = false ∧ bottomMiddle = true ∧
          bottomRight = false ∧ auxiliary = false) ∨
        (topLeft = false ∧ topMiddle = true ∧ topRight = false ∧
          bottomLeft = true ∧ bottomMiddle = false ∧
          bottomRight = true ∧ auxiliary = true) := by
  cases topLeft <;> cases topMiddle <;> cases topRight <;>
    cases bottomLeft <;> cases bottomMiddle <;> cases bottomRight <;>
    cases auxiliary <;> native_decide

/-- Read the two satisfying bit patterns directly from an arbitrary
selection function. -/
theorem fixedRedConnectorHolds_port_pattern
    (selected : FixedRedConnectorTriple → Bool) :
    FixedRedConnectorHolds selected ↔
      (selected .topLeft = true ∧ selected .topMiddle = false ∧
          selected .topRight = true ∧ selected .bottomLeft = false ∧
          selected .bottomMiddle = true ∧
          selected .bottomRight = false ∧ selected .auxiliary = false) ∨
        (selected .topLeft = false ∧ selected .topMiddle = true ∧
          selected .topRight = false ∧ selected .bottomLeft = true ∧
          selected .bottomMiddle = false ∧
          selected .bottomRight = true ∧ selected .auxiliary = true) := by
  let assignment :=
    fixedRedConnectorAssignment
      (selected .topLeft) (selected .topMiddle) (selected .topRight)
      (selected .bottomLeft) (selected .bottomMiddle)
      (selected .bottomRight) (selected .auxiliary)
  have selectedEq : selected = assignment := by
    funext triple
    cases triple <;> rfl
  rw [selectedEq]
  exact fixedRedConnectorAssignment_holds_iff _ _ _ _ _ _ _

/-- Figure 6 admits exactly its two alternating selections. -/
theorem fixedRedConnectorHolds_iff
    (selected : FixedRedConnectorTriple → Bool) :
    FixedRedConnectorHolds selected ↔
      selected = fixedRedConnectorSelection true ∨
        selected = fixedRedConnectorSelection false := by
  constructor
  · intro holds
    rcases (fixedRedConnectorHolds_port_pattern selected).mp holds with
      pattern | pattern
    · left
      funext triple
      cases triple <;> simp_all [fixedRedConnectorSelection]
    · right
      funext triple
      cases triple <;> simp_all [fixedRedConnectorSelection]
  · rintro (rfl | rfl) <;> native_decide

/-- The continuation ports have opposite states, and all three connector
ports have the same state. -/
theorem fixedRedConnector_port_behavior
    (selected : FixedRedConnectorTriple → Bool)
    (holds : FixedRedConnectorHolds selected) :
    selected .topLeft = !selected .bottomLeft ∧
      selected .auxiliary = selected .bottomRight := by
  rcases (fixedRedConnectorHolds_iff selected).mp holds with
    rfl | rfl <;> native_decide

/-- Each of the eight internal elements has degree two. -/
theorem fixedRedConnector_internal_degrees :
    (FixedRedConnectorRed.neighbors .middleRung).length = 2 ∧
      (FixedRedConnectorRed.neighbors .topAuxiliary).length = 2 ∧
      (FixedRedConnectorGreen.neighbors .leftRung).length = 2 ∧
      (FixedRedConnectorGreen.neighbors .topRightLink).length = 2 ∧
      (FixedRedConnectorGreen.neighbors .bottomRightLink).length = 2 ∧
      (FixedRedConnectorBlue.neighbors .topLeftLink).length = 2 ∧
      (FixedRedConnectorBlue.neighbors .bottomLeftLink).length = 2 ∧
      (FixedRedConnectorBlue.neighbors .rightRung).length = 2 := by
  native_decide

end PlanarThreeDM
end LeanTrominoes
