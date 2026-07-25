import LeanTrominoes.PeriodicThreeDM

/-!
# The Dyer--Frieze variable gadget for planar 3DM

This file formalizes the open variable gadget in Figure 10(a) of the paper.
The six white squares are triples arranged in an alternating cycle.  Each
triple contains one of three internal red elements, one of three internal
green elements, and one blue interface element that will be identified with
the surrounding incidence route.

Covering every internal red and green element exactly once leaves exactly two
possible local matchings.  They select alternating triples and therefore
encode the two truth values of the represented SAT variable.  The result is a
finite, exhaustive certificate; no planar routing assumptions enter yet.
-/

namespace LeanTrominoes
namespace PlanarThreeDM

/-- The six white triple vertices of Figure 10(a), in clockwise order. -/
inductive VariableTriple
  | topLeft
  | topRight
  | rightMiddle
  | bottomRight
  | bottomLeft
  | leftMiddle
  deriving DecidableEq, Repr, Fintype

/-- The three internal red elements in the variable gadget. -/
inductive VariableRed
  | right
  | bottom
  | left
  deriving DecidableEq, Repr, Fintype

/-- The three internal green elements in the variable gadget. -/
inductive VariableGreen
  | top
  | right
  | left
  deriving DecidableEq, Repr, Fintype

/-- The blue interface element incident to each variable triple. -/
inductive VariableBluePort
  | topLeft
  | topRight
  | rightMiddle
  | bottomRight
  | bottomLeft
  | leftMiddle
  deriving DecidableEq, Repr, Fintype

/-- The symbolic red, green, and blue references of an open 3DM triple. -/
structure VariableTripleReferences where
  red : VariableRed
  green : VariableGreen
  blue : VariableBluePort
  deriving DecidableEq, Repr

namespace VariableTriple

/-- The element references of each white square in Figure 10(a). -/
def references : VariableTriple → VariableTripleReferences
  | .topLeft =>
      ⟨.left, .top, .topLeft⟩
  | .topRight =>
      ⟨.right, .top, .topRight⟩
  | .rightMiddle =>
      ⟨.right, .right, .rightMiddle⟩
  | .bottomRight =>
      ⟨.bottom, .right, .bottomRight⟩
  | .bottomLeft =>
      ⟨.bottom, .left, .bottomLeft⟩
  | .leftMiddle =>
      ⟨.left, .left, .leftMiddle⟩

/-- Integer-grid coordinates matching the layout of Figure 10(a). -/
def position : VariableTriple → Cell
  | .topLeft => (2, 0)
  | .topRight => (6, 0)
  | .rightMiddle => (8, 2)
  | .bottomRight => (8, 6)
  | .bottomLeft => (0, 6)
  | .leftMiddle => (0, 2)

end VariableTriple

namespace VariableRed

/-- The two triples incident to each internal red element. -/
def neighbors : VariableRed → List VariableTriple
  | .right => [.topRight, .rightMiddle]
  | .bottom => [.bottomRight, .bottomLeft]
  | .left => [.topLeft, .leftMiddle]

/-- Integer-grid coordinates matching the layout of Figure 10(a). -/
def position : VariableRed → Cell
  | .right => (6, 2)
  | .bottom => (4, 6)
  | .left => (2, 2)

end VariableRed

namespace VariableGreen

/-- The two triples incident to each internal green element. -/
def neighbors : VariableGreen → List VariableTriple
  | .top => [.topLeft, .topRight]
  | .right => [.rightMiddle, .bottomRight]
  | .left => [.bottomLeft, .leftMiddle]

/-- Integer-grid coordinates matching the layout of Figure 10(a). -/
def position : VariableGreen → Cell
  | .top => (4, 0)
  | .right => (8, 4)
  | .left => (0, 4)

end VariableGreen

namespace VariableBluePort

/-- The triple incident to each blue interface port. -/
def triple : VariableBluePort → VariableTriple
  | .topLeft => .topLeft
  | .topRight => .topRight
  | .rightMiddle => .rightMiddle
  | .bottomRight => .bottomRight
  | .bottomLeft => .bottomLeft
  | .leftMiddle => .leftMiddle

/-- A point just outside the gadget in the direction of each dotted port. -/
def position : VariableBluePort → Cell
  | .topLeft => (2, -2)
  | .topRight => (6, -2)
  | .rightMiddle => (10, 2)
  | .bottomRight => (10, 6)
  | .bottomLeft => (-2, 6)
  | .leftMiddle => (-2, 2)

end VariableBluePort

/-- A local choice of variable triples covers every internal colored element
exactly once.  Blue ports are intentionally unconstrained: their other
incidences belong to the surrounding routes and clause gadgets. -/
def VariableGadgetHolds
    (selected : VariableTriple → Bool) : Prop :=
  (∀ red, PeriodicOneInThree.ExactlyOne
      ((VariableRed.neighbors red).map selected)) ∧
    ∀ green, PeriodicOneInThree.ExactlyOne
      ((VariableGreen.neighbors green).map selected)

instance (selected : VariableTriple → Bool) :
    Decidable (VariableGadgetHolds selected) := by
  unfold VariableGadgetHolds
  infer_instance

/-- One of the two alternating local matchings.  The Boolean parameter is the
truth value carried by the top-left, right-middle, and bottom-left ports. -/
def variableSelection (value : Bool) : VariableTriple → Bool
  | .topLeft => value
  | .topRight => !value
  | .rightMiddle => value
  | .bottomRight => !value
  | .bottomLeft => value
  | .leftMiddle => !value

/-- Write an arbitrary six Boolean values as a variable-triple selection. -/
private def variableAssignment
    (topLeft topRight rightMiddle bottomRight bottomLeft leftMiddle : Bool) :
    VariableTriple → Bool
  | .topLeft => topLeft
  | .topRight => topRight
  | .rightMiddle => rightMiddle
  | .bottomRight => bottomRight
  | .bottomLeft => bottomLeft
  | .leftMiddle => leftMiddle

/-- Exhaustive six-bit truth table for the internal exact-cover constraints. -/
private theorem variableAssignment_holds_iff
    (topLeft topRight rightMiddle bottomRight bottomLeft leftMiddle : Bool) :
    VariableGadgetHolds
        (variableAssignment topLeft topRight rightMiddle bottomRight
          bottomLeft leftMiddle) ↔
      (topLeft = true ∧ topRight = false ∧ rightMiddle = true ∧
          bottomRight = false ∧ bottomLeft = true ∧ leftMiddle = false) ∨
        (topLeft = false ∧ topRight = true ∧ rightMiddle = false ∧
          bottomRight = true ∧ bottomLeft = false ∧ leftMiddle = true) := by
  cases topLeft <;> cases topRight <;> cases rightMiddle <;>
    cases bottomRight <;> cases bottomLeft <;> cases leftMiddle <;>
    native_decide

/-- The selected state can be read directly at the six interface ports. -/
theorem variableGadgetHolds_port_pattern
    (selected : VariableTriple → Bool) :
    VariableGadgetHolds selected ↔
      (selected .topLeft = true ∧ selected .topRight = false ∧
          selected .rightMiddle = true ∧ selected .bottomRight = false ∧
          selected .bottomLeft = true ∧ selected .leftMiddle = false) ∨
        (selected .topLeft = false ∧ selected .topRight = true ∧
          selected .rightMiddle = false ∧ selected .bottomRight = true ∧
          selected .bottomLeft = false ∧ selected .leftMiddle = true) := by
  let assignment :=
    variableAssignment (selected .topLeft) (selected .topRight)
      (selected .rightMiddle) (selected .bottomRight)
      (selected .bottomLeft) (selected .leftMiddle)
  have selectedEq : selected = assignment := by
    funext triple
    cases triple <;> rfl
  rw [selectedEq]
  exact variableAssignment_holds_iff _ _ _ _ _ _

/-- Figure 10(a) admits exactly the two alternating selections. -/
theorem variableGadgetHolds_iff
    (selected : VariableTriple → Bool) :
    VariableGadgetHolds selected ↔
      selected = variableSelection true ∨
        selected = variableSelection false := by
  constructor
  · intro holds
    rcases (variableGadgetHolds_port_pattern selected).mp holds with
      pattern | pattern
    · left
      funext triple
      cases triple <;> simp_all [variableSelection]
    · right
      funext triple
      cases triple <;> simp_all [variableSelection]
  · rintro (rfl | rfl) <;> native_decide

/-- Every internal red element has degree two inside the variable gadget. -/
theorem variableRed_degree_two (red : VariableRed) :
    (VariableRed.neighbors red).length = 2 := by
  cases red <;> rfl

/-- Every internal green element has degree two inside the variable gadget. -/
theorem variableGreen_degree_two (green : VariableGreen) :
    (VariableGreen.neighbors green).length = 2 := by
  cases green <;> rfl

/-- Each open triple has a distinct blue port. -/
theorem variableBluePort_triple_bijective :
    Function.Bijective VariableBluePort.triple := by
  constructor
  · intro first second equality
    cases first <;> cases second <;> simp_all [VariableBluePort.triple]
  · intro triple
    cases triple <;>
      first
      | exact ⟨.topLeft, rfl⟩
      | exact ⟨.topRight, rfl⟩
      | exact ⟨.rightMiddle, rfl⟩
      | exact ⟨.bottomRight, rfl⟩
      | exact ⟨.bottomLeft, rfl⟩
      | exact ⟨.leftMiddle, rfl⟩

end PlanarThreeDM
end LeanTrominoes
