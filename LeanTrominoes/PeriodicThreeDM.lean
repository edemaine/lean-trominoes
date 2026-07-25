import LeanTrominoes.GadgetLibrary
import LeanTrominoes.PeriodicOneInThree

/-!
# Periodic three-dimensional matching

This file defines the periodic 3DM source used in the paper's reduction to
trichromatic graph orientation.  Each prototype triple names one red, one
green, and one blue element at integer-lattice offsets.  Selecting a triple at
a translate must cover every translated element exactly once.

The associated abstract edge orientation records `true` when an incidence is
directed from its triple toward its colored element.  Triple coherence is the
0-or-3 rule, while exact coverage is precisely the monochromatic 1-in-3 rule.
Geometry and orthogonal routing are deliberately left to later modules.
-/

namespace LeanTrominoes

open Gadget

/-- One colored element occurrence in a prototype triple. -/
structure PeriodicThreeDMReference where
  atom : Nat
  offset : Cell
  deriving DecidableEq, Repr, Inhabited

/-- A prototype triple, with one reference of each color. -/
structure PeriodicThreeDMTriple where
  red : PeriodicThreeDMReference
  green : PeriodicThreeDMReference
  blue : PeriodicThreeDMReference
  deriving DecidableEq, Repr, Inhabited

namespace PeriodicThreeDMTriple

/-- Select the reference of a specified color. -/
def reference (triple : PeriodicThreeDMTriple) : WireColor →
    PeriodicThreeDMReference
  | .red => triple.red
  | .green => triple.green
  | .blue => triple.blue

end PeriodicThreeDMTriple

/-- A finite presentation of an infinite periodic 3DM problem. -/
structure PeriodicThreeDM where
  redCount : Nat
  greenCount : Nat
  blueCount : Nat
  triples : List PeriodicThreeDMTriple
  deriving DecidableEq, Repr

namespace PeriodicThreeDM

/-- Number of prototype elements of a specified color. -/
def elementCount (problem : PeriodicThreeDM) : WireColor → Nat
  | .red => problem.redCount
  | .green => problem.greenCount
  | .blue => problem.blueCount

/-- Every triple reference names an element in the finite presentation. -/
def IsWellFormed (problem : PeriodicThreeDM) : Prop :=
  ∀ triple ∈ problem.triples, ∀ color,
    (triple.reference color).atom < problem.elementCount color

instance (problem : PeriodicThreeDM) :
    Decidable problem.IsWellFormed := by
  unfold IsWellFormed
  infer_instance

/-- An incidence of one prototype element with one prototype triple. -/
structure Incidence where
  tripleIndex : Nat
  offset : Cell
  deriving DecidableEq, Repr

/-- All incidences of one prototype element.  The offset says where the
element lies relative to the triple translate. -/
def incidences (problem : PeriodicThreeDM) (color : WireColor)
    (atom : Nat) : List Incidence :=
  (List.range problem.triples.length).filterMap fun tripleIndex =>
    let reference :=
      (problem.triples.getD tripleIndex default).reference color
    if reference.atom = atom then
      some ⟨tripleIndex, reference.offset⟩
    else
      none

/-- The finite degree of a prototype element in the periodic incidence
graph. -/
def degree (problem : PeriodicThreeDM) (color : WireColor)
    (atom : Nat) : Nat :=
  (problem.incidences color atom).length

/-- The degree-two-or-three restriction used by the exact-one reduction. -/
def DegreeTwoOrThree (problem : PeriodicThreeDM) : Prop :=
  ∀ color atom, atom < problem.elementCount color →
    problem.degree color atom ∈ ([2, 3] : List Nat)

instance (problem : PeriodicThreeDM) :
    Decidable problem.DegreeTwoOrThree := by
  unfold DegreeTwoOrThree
  infer_instance

/-- The degree-three restriction used before conversion to trichromatic graph
orientation. -/
def DegreeThree (problem : PeriodicThreeDM) : Prop :=
  ∀ color atom, atom < problem.elementCount color →
    problem.degree color atom = 3

instance (problem : PeriodicThreeDM) :
    Decidable problem.DegreeThree := by
  unfold DegreeThree
  infer_instance

/-- A translated triple is either selected or not selected. -/
abbrev MatchingAssignment (_instance : PeriodicThreeDM) :=
  Nat → Cell → Bool

/-- An abstract orientation value for every colored incidence.  `true` means
the edge points from its triple endpoint toward its element endpoint. -/
abbrev Orientation (_instance : PeriodicThreeDM) :=
  Nat → Cell → WireColor → Bool

/-- Read the values on every edge incident to one translated element. -/
def incidentValues (problem : PeriodicThreeDM)
    (values : problem.Orientation) (color : WireColor)
    (atom : Nat) (cell : Cell) : List Bool :=
  (problem.incidences color atom).map fun incidence =>
    values incidence.tripleIndex
      (Cell.sub cell incidence.offset) color

/-- Every translated element sees exactly one selected/toward-element
incidence. -/
def CoversElements (problem : PeriodicThreeDM)
    (values : problem.Orientation) : Prop :=
  ∀ color atom, atom < problem.elementCount color → ∀ cell,
    PeriodicOneInThree.ExactlyOne
      (problem.incidentValues values color atom cell)

/-- Forget incidence color and use one matching-selection value on all three
edges of a triple. -/
def liftAssignment (problem : PeriodicThreeDM)
    (assignment : problem.MatchingAssignment) : problem.Orientation :=
  fun tripleIndex cell _color => assignment tripleIndex cell

/-- A matching selects triples so that every translated element is covered
exactly once. -/
def Satisfies (problem : PeriodicThreeDM)
    (assignment : problem.MatchingAssignment) : Prop :=
  problem.CoversElements (problem.liftAssignment assignment)

/-- The infinite periodic 3DM instance admits a perfect matching. -/
def Satisfiable (problem : PeriodicThreeDM) : Prop :=
  ∃ assignment, problem.Satisfies assignment

/-- At every actual triple translate, all three edge directions agree.  In
ordinary inward-orientation language, the triple has indegree zero or three. -/
def TripleCoherent (problem : PeriodicThreeDM)
    (orientation : problem.Orientation) : Prop :=
  ∀ tripleIndex, tripleIndex < problem.triples.length → ∀ cell,
    orientation tripleIndex cell .red =
        orientation tripleIndex cell .green ∧
      orientation tripleIndex cell .green =
        orientation tripleIndex cell .blue

/-- The abstract trichromatic graph-orientation constraints associated with
the periodic 3DM incidence graph. -/
def IsOrientation (problem : PeriodicThreeDM)
    (orientation : problem.Orientation) : Prop :=
  problem.TripleCoherent orientation ∧
    problem.CoversElements orientation

/-- The periodic 3DM incidence graph has a valid trichromatic orientation. -/
def HasOrientation (problem : PeriodicThreeDM) : Prop :=
  ∃ orientation, problem.IsOrientation orientation

/-- Restrict an abstract orientation to its red incidence at each triple. -/
def restrictOrientation (problem : PeriodicThreeDM)
    (orientation : problem.Orientation) : problem.MatchingAssignment :=
  fun tripleIndex cell => orientation tripleIndex cell .red

/-- Every recorded incidence refers to an actual prototype triple. -/
theorem incidence_tripleIndex_lt (problem : PeriodicThreeDM)
    (color : WireColor) (atom : Nat) {incidence : Incidence}
    (member : incidence ∈ problem.incidences color atom) :
    incidence.tripleIndex < problem.triples.length := by
  simp only [incidences, List.mem_filterMap] at member
  rcases member with ⟨tripleIndex, indexMember, produced⟩
  have indexLt := List.mem_range.mp indexMember
  split at produced
  · simp only [Option.some.injEq] at produced
    subst incidence
    exact indexLt
  · contradiction

/-- A coherent orientation agrees with its red restriction on every actual
colored incidence. -/
theorem restrictOrientation_incidence_value
    (problem : PeriodicThreeDM) (orientation : problem.Orientation)
    (coherent : problem.TripleCoherent orientation)
    (color : WireColor) (atom : Nat) (cell : Cell)
    {incidence : Incidence}
    (member : incidence ∈ problem.incidences color atom) :
    problem.liftAssignment (problem.restrictOrientation orientation)
        incidence.tripleIndex (Cell.sub cell incidence.offset) color =
      orientation incidence.tripleIndex
        (Cell.sub cell incidence.offset) color := by
  have indexLt :=
    incidence_tripleIndex_lt problem color atom member
  have agrees := coherent incidence.tripleIndex indexLt
    (Cell.sub cell incidence.offset)
  cases color with
  | red => rfl
  | green => exact agrees.1
  | blue => exact agrees.1.trans agrees.2

/-- Restriction preserves the complete list of values incident to every
element. -/
theorem incidentValues_lift_restrict
    (problem : PeriodicThreeDM) (orientation : problem.Orientation)
    (coherent : problem.TripleCoherent orientation)
    (color : WireColor) (atom : Nat) (cell : Cell) :
    problem.incidentValues
        (problem.liftAssignment
          (problem.restrictOrientation orientation))
        color atom cell =
      problem.incidentValues orientation color atom cell := by
  unfold incidentValues
  apply List.map_congr_left
  intro incidence member
  exact restrictOrientation_incidence_value
    problem orientation coherent color atom cell member

/-- A perfect periodic 3D matching is exactly an orientation satisfying the
trichromatic 0-or-3 and monochromatic 1-in-3 constraints. -/
theorem satisfiable_iff_hasOrientation (problem : PeriodicThreeDM) :
    problem.Satisfiable ↔ problem.HasOrientation := by
  constructor
  · rintro ⟨assignment, covers⟩
    refine ⟨problem.liftAssignment assignment, ?_, covers⟩
    intro tripleIndex indexLt cell
    exact ⟨rfl, rfl⟩
  · rintro ⟨orientation, coherent, covers⟩
    refine ⟨problem.restrictOrientation orientation, ?_⟩
    intro color atom atomLt cell
    rw [incidentValues_lift_restrict
      problem orientation coherent color atom cell]
    exact covers color atom atomLt cell

end PeriodicThreeDM
end LeanTrominoes
