import LeanTrominoes.PeriodicOneInThreeToThreeDMTyped

/-!
# Exact-cover semantics for the typed periodic 3DM presentation

The reduction is first assembled with meaningful element and triple types.
This file gives that presentation its direct periodic exact-cover semantics,
before the finite types are encoded by natural numbers for
`PeriodicThreeDM`.

An incidence offset records the element cell relative to the triple cell.
Thus an element at `cell` reads its incident triple at
`cell - incidence.offset`, exactly as in the natural-number presentation.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreeToThreeDM

/-- One typed incidence with a prototype triple and a lattice offset. -/
structure Incidence (Variable : Type*) where
  triple : Triple Variable
  offset : Cell
  deriving DecidableEq, Repr

/-- The red incidences of one typed prototype element. -/
def TypedPeriodicThreeDM.redIncidences {Variable : Type*}
    [DecidableEq Variable] (problem : TypedPeriodicThreeDM Variable)
    (atom : RedElement Variable) : List (Incidence Variable) :=
  problem.triples.filterMap fun triple =>
    let reference := (problem.references triple).red
    if reference.atom = atom then
      some ⟨triple, reference.offset⟩
    else
      none

/-- The green incidences of one typed prototype element. -/
def TypedPeriodicThreeDM.greenIncidences {Variable : Type*}
    [DecidableEq Variable] (problem : TypedPeriodicThreeDM Variable)
    (atom : GreenElement Variable) : List (Incidence Variable) :=
  problem.triples.filterMap fun triple =>
    let reference := (problem.references triple).green
    if reference.atom = atom then
      some ⟨triple, reference.offset⟩
    else
      none

/-- The blue incidences of one typed prototype element. -/
def TypedPeriodicThreeDM.blueIncidences {Variable : Type*}
    [DecidableEq Variable] (problem : TypedPeriodicThreeDM Variable)
    (atom : BlueElement Variable) : List (Incidence Variable) :=
  problem.triples.filterMap fun triple =>
    let reference := (problem.references triple).blue
    if reference.atom = atom then
      some ⟨triple, reference.offset⟩
    else
      none

/-- A translated typed triple is selected or unselected. -/
abbrev TypedPeriodicThreeDM.MatchingAssignment {Variable : Type*}
    (_problem : TypedPeriodicThreeDM Variable) :=
  Triple Variable → Cell → Bool

/-- Read the selection at the translated triple incident to an element cell. -/
def TypedPeriodicThreeDM.incidenceValue {Variable : Type*}
    (problem : TypedPeriodicThreeDM Variable)
    (assignment : problem.MatchingAssignment)
    (incidence : Incidence Variable) (cell : Cell) : Bool :=
  assignment incidence.triple (Cell.sub cell incidence.offset)

/-- Values on all red incidences of one translated element. -/
def TypedPeriodicThreeDM.redIncidentValues {Variable : Type*}
    [DecidableEq Variable] (problem : TypedPeriodicThreeDM Variable)
    (assignment : problem.MatchingAssignment)
    (atom : RedElement Variable) (cell : Cell) : List Bool :=
  (problem.redIncidences atom).map fun incidence =>
    problem.incidenceValue assignment incidence cell

/-- Values on all green incidences of one translated element. -/
def TypedPeriodicThreeDM.greenIncidentValues {Variable : Type*}
    [DecidableEq Variable] (problem : TypedPeriodicThreeDM Variable)
    (assignment : problem.MatchingAssignment)
    (atom : GreenElement Variable) (cell : Cell) : List Bool :=
  (problem.greenIncidences atom).map fun incidence =>
    problem.incidenceValue assignment incidence cell

/-- Values on all blue incidences of one translated element. -/
def TypedPeriodicThreeDM.blueIncidentValues {Variable : Type*}
    [DecidableEq Variable] (problem : TypedPeriodicThreeDM Variable)
    (assignment : problem.MatchingAssignment)
    (atom : BlueElement Variable) (cell : Cell) : List Bool :=
  (problem.blueIncidences atom).map fun incidence =>
    problem.incidenceValue assignment incidence cell

/-- Every listed translated red element is covered exactly once. -/
def TypedPeriodicThreeDM.CoversRed {Variable : Type*}
    [DecidableEq Variable] (problem : TypedPeriodicThreeDM Variable)
    (assignment : problem.MatchingAssignment) : Prop :=
  ∀ atom ∈ problem.redElements, ∀ cell,
    PeriodicOneInThree.ExactlyOne
      (problem.redIncidentValues assignment atom cell)

/-- Every listed translated green element is covered exactly once. -/
def TypedPeriodicThreeDM.CoversGreen {Variable : Type*}
    [DecidableEq Variable] (problem : TypedPeriodicThreeDM Variable)
    (assignment : problem.MatchingAssignment) : Prop :=
  ∀ atom ∈ problem.greenElements, ∀ cell,
    PeriodicOneInThree.ExactlyOne
      (problem.greenIncidentValues assignment atom cell)

/-- Every listed translated blue element is covered exactly once. -/
def TypedPeriodicThreeDM.CoversBlue {Variable : Type*}
    [DecidableEq Variable] (problem : TypedPeriodicThreeDM Variable)
    (assignment : problem.MatchingAssignment) : Prop :=
  ∀ atom ∈ problem.blueElements, ∀ cell,
    PeriodicOneInThree.ExactlyOne
      (problem.blueIncidentValues assignment atom cell)

/-- A typed periodic matching covers every listed colored element once. -/
def TypedPeriodicThreeDM.Satisfies {Variable : Type*}
    [DecidableEq Variable] (problem : TypedPeriodicThreeDM Variable)
    (assignment : problem.MatchingAssignment) : Prop :=
  problem.CoversRed assignment ∧
    problem.CoversGreen assignment ∧
    problem.CoversBlue assignment

/-- The typed periodic 3DM presentation admits a perfect matching. -/
def TypedPeriodicThreeDM.Satisfiable {Variable : Type*}
    [DecidableEq Variable] (problem : TypedPeriodicThreeDM Variable) : Prop :=
  ∃ assignment, problem.Satisfies assignment

/-- Every triple reference names a listed typed element. -/
def TypedPeriodicThreeDM.IsWellFormed {Variable : Type*}
    [DecidableEq Variable] (problem : TypedPeriodicThreeDM Variable) : Prop :=
  ∀ triple ∈ problem.triples,
    (problem.references triple).red.atom ∈ problem.redElements ∧
      (problem.references triple).green.atom ∈ problem.greenElements ∧
      (problem.references triple).blue.atom ∈ problem.blueElements

/-- Every listed typed colored element has degree two or three. -/
def TypedPeriodicThreeDM.DegreeTwoOrThree {Variable : Type*}
    [DecidableEq Variable] (problem : TypedPeriodicThreeDM Variable) : Prop :=
  (∀ atom ∈ problem.redElements,
      (problem.redIncidences atom).length ∈ ([2, 3] : List Nat)) ∧
    (∀ atom ∈ problem.greenElements,
      (problem.greenIncidences atom).length ∈ ([2, 3] : List Nat)) ∧
    (∀ atom ∈ problem.blueElements,
      (problem.blueIncidences atom).length ∈ ([2, 3] : List Nat))

instance {Variable : Type*} [DecidableEq Variable]
    (problem : TypedPeriodicThreeDM Variable) :
    Decidable problem.IsWellFormed := by
  unfold TypedPeriodicThreeDM.IsWellFormed
  infer_instance

instance {Variable : Type*} [DecidableEq Variable]
    (problem : TypedPeriodicThreeDM Variable) :
    Decidable problem.DegreeTwoOrThree := by
  unfold TypedPeriodicThreeDM.DegreeTwoOrThree
  infer_instance

/-- Subtracting a reversed literal offset locates the variable triple at the
literal cell relative to its clause translate. -/
@[simp]
theorem sub_reverseOffset (translate offset : Cell) :
    Cell.sub translate (reverseOffset offset) =
      Cell.add translate offset := by
  rcases translate with ⟨x, y⟩
  rcases offset with ⟨dx, dy⟩
  simp [Cell.sub, Cell.add, reverseOffset]

end PeriodicOneInThreeToThreeDM
end LeanTrominoes
