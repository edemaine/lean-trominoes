/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMTyped

/-!
# Exact-cover semantics for the typed planar periodic 3DM presentation

This file gives the inspectable colored presentation its direct periodic
matching semantics.  A reference offset is the element cell relative to the
triple cell, so an element translated to `cell` reads an incident triple at
`cell - offset`.

The definitions deliberately precede the natural-number encoding.  This
keeps the correctness proof phrased in terms of variable modules, cycle
links, and clause terminals rather than numeric tags.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

/-- One typed incidence with a prototype triple and its element-relative
offset. -/
structure Incidence (Variable : Type*) where
  triple : Triple Variable
  offset : Cell
  deriving DecidableEq, Repr

/-- Red incidences of one typed prototype element. -/
def TypedProblem.redIncidences {Variable : Type*}
    [DecidableEq Variable] (problem : TypedProblem Variable)
    (atom : RedElement Variable) : List (Incidence Variable) :=
  problem.triples.filterMap fun triple =>
    let reference := (problem.references triple).red
    if reference.atom = atom then
      some ⟨triple, reference.offset⟩
    else
      none

/-- Green incidences of one typed prototype element. -/
def TypedProblem.greenIncidences {Variable : Type*}
    [DecidableEq Variable] (problem : TypedProblem Variable)
    (atom : GreenElement Variable) : List (Incidence Variable) :=
  problem.triples.filterMap fun triple =>
    let reference := (problem.references triple).green
    if reference.atom = atom then
      some ⟨triple, reference.offset⟩
    else
      none

/-- Blue incidences of one typed prototype element. -/
def TypedProblem.blueIncidences {Variable : Type*}
    [DecidableEq Variable] (problem : TypedProblem Variable)
    (atom : BlueElement Variable) : List (Incidence Variable) :=
  problem.triples.filterMap fun triple =>
    let reference := (problem.references triple).blue
    if reference.atom = atom then
      some ⟨triple, reference.offset⟩
    else
      none

/-- Selection of each translated typed triple. -/
abbrev TypedProblem.MatchingAssignment {Variable : Type*}
    (_problem : TypedProblem Variable) :=
  Triple Variable → Cell → Bool

/-- Selection at the translated triple incident to an element cell. -/
def TypedProblem.incidenceValue {Variable : Type*}
    (problem : TypedProblem Variable)
    (assignment : problem.MatchingAssignment)
    (incidence : Incidence Variable) (cell : Cell) : Bool :=
  assignment incidence.triple (Cell.sub cell incidence.offset)

/-- Values on all red incidences of one translated element. -/
def TypedProblem.redIncidentValues {Variable : Type*}
    [DecidableEq Variable] (problem : TypedProblem Variable)
    (assignment : problem.MatchingAssignment)
    (atom : RedElement Variable) (cell : Cell) : List Bool :=
  (problem.redIncidences atom).map fun incidence =>
    problem.incidenceValue assignment incidence cell

/-- Values on all green incidences of one translated element. -/
def TypedProblem.greenIncidentValues {Variable : Type*}
    [DecidableEq Variable] (problem : TypedProblem Variable)
    (assignment : problem.MatchingAssignment)
    (atom : GreenElement Variable) (cell : Cell) : List Bool :=
  (problem.greenIncidences atom).map fun incidence =>
    problem.incidenceValue assignment incidence cell

/-- Values on all blue incidences of one translated element. -/
def TypedProblem.blueIncidentValues {Variable : Type*}
    [DecidableEq Variable] (problem : TypedProblem Variable)
    (assignment : problem.MatchingAssignment)
    (atom : BlueElement Variable) (cell : Cell) : List Bool :=
  (problem.blueIncidences atom).map fun incidence =>
    problem.incidenceValue assignment incidence cell

/-- Every listed translated red element is covered exactly once. -/
def TypedProblem.CoversRed {Variable : Type*}
    [DecidableEq Variable] (problem : TypedProblem Variable)
    (assignment : problem.MatchingAssignment) : Prop :=
  ∀ atom ∈ problem.redElements, ∀ cell,
    PeriodicOneInThree.ExactlyOne
      (problem.redIncidentValues assignment atom cell)

/-- Every listed translated green element is covered exactly once. -/
def TypedProblem.CoversGreen {Variable : Type*}
    [DecidableEq Variable] (problem : TypedProblem Variable)
    (assignment : problem.MatchingAssignment) : Prop :=
  ∀ atom ∈ problem.greenElements, ∀ cell,
    PeriodicOneInThree.ExactlyOne
      (problem.greenIncidentValues assignment atom cell)

/-- Every listed translated blue element is covered exactly once. -/
def TypedProblem.CoversBlue {Variable : Type*}
    [DecidableEq Variable] (problem : TypedProblem Variable)
    (assignment : problem.MatchingAssignment) : Prop :=
  ∀ atom ∈ problem.blueElements, ∀ cell,
    PeriodicOneInThree.ExactlyOne
      (problem.blueIncidentValues assignment atom cell)

/-- A typed periodic matching covers every listed colored element exactly
once. -/
def TypedProblem.Satisfies {Variable : Type*}
    [DecidableEq Variable] (problem : TypedProblem Variable)
    (assignment : problem.MatchingAssignment) : Prop :=
  problem.CoversRed assignment ∧
    problem.CoversGreen assignment ∧
    problem.CoversBlue assignment

/-- The typed planar periodic 3DM presentation admits a perfect matching. -/
def TypedProblem.Satisfiable {Variable : Type*}
    [DecidableEq Variable] (problem : TypedProblem Variable) : Prop :=
  ∃ assignment, problem.Satisfies assignment

/-- Every triple reference names a listed typed element. -/
def TypedProblem.IsWellFormed {Variable : Type*}
    [DecidableEq Variable] (problem : TypedProblem Variable) : Prop :=
  ∀ triple ∈ problem.triples,
    (problem.references triple).red.atom ∈ problem.redElements ∧
      (problem.references triple).green.atom ∈ problem.greenElements ∧
      (problem.references triple).blue.atom ∈ problem.blueElements

/-- Every listed typed colored element has degree two or three. -/
def TypedProblem.DegreeTwoOrThree {Variable : Type*}
    [DecidableEq Variable] (problem : TypedProblem Variable) : Prop :=
  (∀ atom ∈ problem.redElements,
      (problem.redIncidences atom).length ∈ ([2, 3] : List Nat)) ∧
    (∀ atom ∈ problem.greenElements,
      (problem.greenIncidences atom).length ∈ ([2, 3] : List Nat)) ∧
    (∀ atom ∈ problem.blueElements,
      (problem.blueIncidences atom).length ∈ ([2, 3] : List Nat))

instance {Variable : Type*} [DecidableEq Variable]
    (problem : TypedProblem Variable) :
    Decidable problem.IsWellFormed := by
  unfold TypedProblem.IsWellFormed
  infer_instance

instance {Variable : Type*} [DecidableEq Variable]
    (problem : TypedProblem Variable) :
    Decidable problem.DegreeTwoOrThree := by
  unfold TypedProblem.DegreeTwoOrThree
  infer_instance

/-- An occurrence reference stored at its variable translate and pointing
back by the negated literal offset reads a triple at the literal cell. -/
@[simp]
theorem sub_occurrenceReverseOffset
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (slot : OccurrenceSlot) (translate : Cell)
    (tagged : TaggedOccurrence Variable)
    (lookup : occurrenceAt source atom slot = some tagged) :
    Cell.sub translate
        (occurrenceReverseOffset source atom slot) =
      Cell.add translate tagged.1.offset := by
  simp only [occurrenceReverseOffset, lookup]
  rcases translate with ⟨x, y⟩
  rcases tagged.1.offset with ⟨dx, dy⟩
  simp [Cell.sub, Cell.add,
    PeriodicOneInThreeToThreeDM.reverseOffset]

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
