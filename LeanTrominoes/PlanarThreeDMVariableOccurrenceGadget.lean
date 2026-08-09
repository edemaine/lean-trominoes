import LeanTrominoes.PlanarThreeDMConnectorGadget

/-!
# Ordinary Dyer--Frieze variable-occurrence connectors

A variable cycle is assembled from occurrence modules with red continuation
elements.  If a clause terminal needs its fixed element to be blue or green,
an ordinary module consists of two consecutive cycle triples and one
auxiliary triple.  The two internal degree-two elements force the three
connector ports to be covered all together or not at all, while the two red
continuation ports have opposite states.

The fixed-red case cannot use this three-triple shape with red continuation
ports; that is exactly the purpose of the larger Figure 6 detour formalized
in `PlanarThreeDMConnectorGadget`.
-/

namespace LeanTrominoes
namespace PlanarThreeDM

/-- The two fixed-color variants supported by the ordinary occurrence
module. -/
inductive VariableOccurrenceVariant
  | fixedGreen
  | fixedBlue
  deriving DecidableEq, Repr, Fintype

/-- The two cycle triples and their auxiliary terminal triple. -/
inductive VariableOccurrenceTriple
  | first
  | second
  | auxiliary
  deriving DecidableEq, Repr, Fintype

/-- Unified element names for both color variants. -/
inductive VariableOccurrenceElement
  | leftContinuation
  | rightContinuation
  | cycleShared
  | auxiliaryShared
  | connectorRed
  | connectorGreen
  | connectorBlue
  deriving DecidableEq, Repr, Fintype

/-- One red, green, and blue element reference. -/
structure VariableOccurrenceReferences where
  red : VariableOccurrenceElement
  green : VariableOccurrenceElement
  blue : VariableOccurrenceElement
  deriving DecidableEq, Repr

namespace VariableOccurrenceVariant

/-- The connector element incident to the first cycle triple is blue in the
shared rotated occurrence tree. -/
def fixedColor : VariableOccurrenceVariant → Gadget.WireColor
  | .fixedGreen => .blue
  | .fixedBlue => .blue

end VariableOccurrenceVariant

namespace VariableOccurrenceTriple

/-- Explicit colored references for both ordinary connector variants. -/
def references :
    VariableOccurrenceVariant →
      VariableOccurrenceTriple → VariableOccurrenceReferences
  | .fixedGreen, .first =>
      ⟨.leftContinuation, .cycleShared, .connectorBlue⟩
  | .fixedGreen, .second =>
      ⟨.rightContinuation, .cycleShared, .auxiliaryShared⟩
  | .fixedGreen, .auxiliary =>
      ⟨.connectorRed, .connectorGreen, .auxiliaryShared⟩
  | .fixedBlue, .first =>
      ⟨.leftContinuation, .cycleShared, .connectorBlue⟩
  | .fixedBlue, .second =>
      ⟨.rightContinuation, .cycleShared, .auxiliaryShared⟩
  | .fixedBlue, .auxiliary =>
      ⟨.connectorRed, .connectorGreen, .auxiliaryShared⟩

/-- Integer coordinates for the triangular planar layout. -/
def position : VariableOccurrenceTriple → Cell
  | .first => (0, 0)
  | .second => (4, 0)
  | .auxiliary => (4, 4)

end VariableOccurrenceTriple

namespace VariableOccurrenceElement

/-- The color of each element in the selected variant. -/
def color :
    VariableOccurrenceVariant →
      VariableOccurrenceElement → Gadget.WireColor
  | _, .leftContinuation => .red
  | _, .rightContinuation => .red
  | .fixedGreen, .cycleShared => .green
  | .fixedGreen, .auxiliaryShared => .blue
  | .fixedBlue, .cycleShared => .green
  | .fixedBlue, .auxiliaryShared => .blue
  | _, .connectorRed => .red
  | _, .connectorGreen => .green
  | _, .connectorBlue => .blue

/-- Local incidence lists.  Only which colored connector port is fixed
depends on the variant. -/
def neighbors :
    VariableOccurrenceVariant →
      VariableOccurrenceElement → List VariableOccurrenceTriple
  | _, .leftContinuation => [.first]
  | _, .rightContinuation => [.second]
  | _, .cycleShared => [.first, .second]
  | _, .auxiliaryShared => [.second, .auxiliary]
  | _, .connectorRed => [.auxiliary]
  | .fixedGreen, .connectorGreen => [.auxiliary]
  | .fixedBlue, .connectorGreen => [.auxiliary]
  | .fixedGreen, .connectorBlue => [.first]
  | .fixedBlue, .connectorBlue => [.first]

/-- Integer coordinates for the local incidence layout. -/
def position : VariableOccurrenceElement → Cell
  | .leftContinuation => (-2, 0)
  | .rightContinuation => (6, 0)
  | .cycleShared => (2, 0)
  | .auxiliaryShared => (4, 2)
  | .connectorRed => (2, 4)
  | .connectorGreen => (4, 6)
  | .connectorBlue => (6, 4)

end VariableOccurrenceElement

/-- Reference fields have their advertised colors. -/
theorem variableOccurrence_reference_colors
    (variant : VariableOccurrenceVariant)
    (triple : VariableOccurrenceTriple) :
    (triple.references variant).red.color variant = .red ∧
      (triple.references variant).green.color variant = .green ∧
      (triple.references variant).blue.color variant = .blue := by
  cases variant <;> cases triple <;> native_decide

/-- Red reference fields agree with the local incidence lists. -/
theorem variableOccurrence_mem_red_neighbors_iff
    (variant : VariableOccurrenceVariant)
    (triple : VariableOccurrenceTriple)
    (element : VariableOccurrenceElement)
    (red : element.color variant = .red) :
    triple ∈ element.neighbors variant ↔
      (triple.references variant).red = element := by
  cases variant <;> cases triple <;> cases element <;>
    simp_all [VariableOccurrenceElement.color,
      VariableOccurrenceElement.neighbors,
      VariableOccurrenceTriple.references]

/-- Green reference fields agree with the local incidence lists. -/
theorem variableOccurrence_mem_green_neighbors_iff
    (variant : VariableOccurrenceVariant)
    (triple : VariableOccurrenceTriple)
    (element : VariableOccurrenceElement)
    (green : element.color variant = .green) :
    triple ∈ element.neighbors variant ↔
      (triple.references variant).green = element := by
  cases variant <;> cases triple <;> cases element <;>
    simp_all [VariableOccurrenceElement.color,
      VariableOccurrenceElement.neighbors,
      VariableOccurrenceTriple.references]

/-- Blue reference fields agree with the local incidence lists. -/
theorem variableOccurrence_mem_blue_neighbors_iff
    (variant : VariableOccurrenceVariant)
    (triple : VariableOccurrenceTriple)
    (element : VariableOccurrenceElement)
    (blue : element.color variant = .blue) :
    triple ∈ element.neighbors variant ↔
      (triple.references variant).blue = element := by
  cases variant <;> cases triple <;> cases element <;>
    simp_all [VariableOccurrenceElement.color,
      VariableOccurrenceElement.neighbors,
      VariableOccurrenceTriple.references]

/-- Exact coverage of the two local degree-two elements. -/
def VariableOccurrenceHolds
    (selected : VariableOccurrenceTriple → Bool) : Prop :=
  PeriodicOneInThree.ExactlyOne
      ((VariableOccurrenceElement.neighbors
        .fixedBlue .cycleShared).map selected) ∧
    PeriodicOneInThree.ExactlyOne
      ((VariableOccurrenceElement.neighbors
        .fixedBlue .auxiliaryShared).map selected)

instance (selected : VariableOccurrenceTriple → Bool) :
    Decidable (VariableOccurrenceHolds selected) := by
  unfold VariableOccurrenceHolds
  infer_instance

/-- The occurrence selection determined by its first cycle triple. -/
def variableOccurrenceSelection
    (value : Bool) : VariableOccurrenceTriple → Bool
  | .first => value
  | .second => !value
  | .auxiliary => value

/-- Write three Boolean values as an occurrence selection. -/
private def variableOccurrenceAssignment
    (first second auxiliary : Bool) :
    VariableOccurrenceTriple → Bool
  | .first => first
  | .second => second
  | .auxiliary => auxiliary

/-- Exhaustive three-bit truth table for the ordinary occurrence module. -/
private theorem variableOccurrenceAssignment_holds_iff
    (first second auxiliary : Bool) :
    VariableOccurrenceHolds
        (variableOccurrenceAssignment first second auxiliary) ↔
      (first = true ∧ second = false ∧ auxiliary = true) ∨
        (first = false ∧ second = true ∧ auxiliary = false) := by
  cases first <;> cases second <;> cases auxiliary <;> native_decide

/-- Read the two satisfying bit patterns from an arbitrary selection. -/
theorem variableOccurrenceHolds_port_pattern
    (selected : VariableOccurrenceTriple → Bool) :
    VariableOccurrenceHolds selected ↔
      (selected .first = true ∧ selected .second = false ∧
          selected .auxiliary = true) ∨
        (selected .first = false ∧ selected .second = true ∧
          selected .auxiliary = false) := by
  let assignment :=
    variableOccurrenceAssignment
      (selected .first) (selected .second) (selected .auxiliary)
  have selectedEq : selected = assignment := by
    funext triple
    cases triple <;> rfl
  rw [selectedEq]
  exact variableOccurrenceAssignment_holds_iff _ _ _

/-- The ordinary module admits exactly two complementary cycle states. -/
theorem variableOccurrenceHolds_iff
    (selected : VariableOccurrenceTriple → Bool) :
    VariableOccurrenceHolds selected ↔
      selected = variableOccurrenceSelection true ∨
        selected = variableOccurrenceSelection false := by
  constructor
  · intro holds
    rcases (variableOccurrenceHolds_port_pattern selected).mp holds with
      pattern | pattern
    · left
      funext triple
      cases triple <;> simp_all [variableOccurrenceSelection]
    · right
      funext triple
      cases triple <;> simp_all [variableOccurrenceSelection]
  · rintro (rfl | rfl) <;> native_decide

/-- The two continuation ports are complementary and every colored connector
port has the same internally-covered state. -/
theorem variableOccurrence_port_behavior
    (selected : VariableOccurrenceTriple → Bool)
    (holds : VariableOccurrenceHolds selected) :
    selected .first = !selected .second ∧
      selected .first = selected .auxiliary := by
  rcases (variableOccurrenceHolds_iff selected).mp holds with
    rfl | rfl <;> native_decide

/-- Both internal elements have degree two; all five ports have one local
incidence and gain their remaining incidences during assembly. -/
theorem variableOccurrence_local_degrees
    (variant : VariableOccurrenceVariant) :
    (VariableOccurrenceElement.neighbors variant .cycleShared).length = 2 ∧
      (VariableOccurrenceElement.neighbors
        variant .auxiliaryShared).length = 2 ∧
      (VariableOccurrenceElement.neighbors
        variant .leftContinuation).length = 1 ∧
      (VariableOccurrenceElement.neighbors
        variant .rightContinuation).length = 1 ∧
      (VariableOccurrenceElement.neighbors
        variant .connectorRed).length = 1 ∧
      (VariableOccurrenceElement.neighbors
        variant .connectorGreen).length = 1 ∧
      (VariableOccurrenceElement.neighbors
        variant .connectorBlue).length = 1 := by
  cases variant <;> native_decide

end PlanarThreeDM
end LeanTrominoes
