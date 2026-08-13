/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMGraphOrientation

/-!
# Suppressing degree-two vertices in periodic 3DM incidence graphs

The reduction from planar 3DM to trichromatic graph orientation contracts
every degree-two colored vertex.  In half-edge language, contraction replaces
the exact-one constraint on its two incidences by the wire constraint that the
two endpoint values are opposite.  Degree-three colored vertices remain
monochromatic exact-one vertices.

This file isolates that semantic step from the geometric concatenation of
the two incident routes.  Orientations are still indexed by the original
incidence tags, which is exactly the endpoint representation consumed by a
later normalized drawing.
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- The local constraint after degree-two colored vertices have been
suppressed.  Two incidences are the two ends of one directed wire; three
incidences remain a monochromatic exact-one vertex. -/
def SuppressedElementConstraint (values : List Bool) : Prop :=
  match values with
  | [first, second] => first ≠ second
  | [first, second, third] =>
      PeriodicOneInThree.ExactlyOne [first, second, third]
  | _ => False

instance (values : List Bool) :
    Decidable (SuppressedElementConstraint values) := by
  unfold SuppressedElementConstraint
  split <;> infer_instance

@[simp]
theorem suppressedElementConstraint_pair_iff
    (first second : Bool) :
    SuppressedElementConstraint [first, second] ↔ first ≠ second := by
  rfl

@[simp]
theorem suppressedElementConstraint_triple_iff
    (first second third : Bool) :
    SuppressedElementConstraint [first, second, third] ↔
      PeriodicOneInThree.ExactlyOne [first, second, third] := by
  rfl

/-- On two Boolean incidences, exact-one is precisely the directed-wire
condition that the two inward endpoint values differ. -/
@[simp]
theorem exactlyOne_pair_iff_ne (first second : Bool) :
    PeriodicOneInThree.ExactlyOne [first, second] ↔ first ≠ second := by
  cases first <;> cases second <;>
    simp [PeriodicOneInThree.ExactlyOne]

/-- Under the promised degree-two-or-three restriction, exact cover at one
colored element is equivalent to its post-contraction local constraint. -/
theorem exactlyOne_iff_suppressedElementConstraint
    (values : List Bool)
    (length : values.length = 2 ∨ values.length = 3) :
    PeriodicOneInThree.ExactlyOne values ↔
      SuppressedElementConstraint values := by
  rcases length with lengthTwo | lengthThree
  · rcases values with _ | ⟨first, values⟩
    · simp at lengthTwo
    rcases values with _ | ⟨second, values⟩
    · simp at lengthTwo
    rcases values with _ | ⟨third, values⟩
    · exact exactlyOne_pair_iff_ne first second
    simp at lengthTwo
  · rcases values with _ | ⟨first, values⟩
    · simp at lengthThree
    rcases values with _ | ⟨second, values⟩
    · simp at lengthThree
    rcases values with _ | ⟨third, values⟩
    · simp at lengthThree
    rcases values with _ | ⟨fourth, values⟩
    · rfl
    simp at lengthThree

/-- Every colored element satisfies its post-contraction wire-or-vertex
constraint at every lattice translate. -/
def SuppressedCoversElements (problem : PeriodicThreeDM)
    (values : problem.GraphOrientation) : Prop :=
  ∀ color atom, atom < problem.elementCount color → ∀ cell,
    SuppressedElementConstraint
      (problem.graphIncidentValues values color atom cell)

/-- The orientation constraints after all degree-two colored vertices are
suppressed. -/
def IsSuppressedOrientation (problem : PeriodicThreeDM)
    (values : problem.GraphOrientation) : Prop :=
  problem.GraphTripleCoherent values ∧
    problem.SuppressedCoversElements values

/-- The contracted trichromatic graph admits an orientation, represented by
the values at the retained route endpoints. -/
def HasSuppressedOrientation (problem : PeriodicThreeDM) : Prop :=
  ∃ values, problem.IsSuppressedOrientation values

/-- The number of values read at one translated colored element is its
finite prototype degree. -/
theorem graphIncidentValues_length (problem : PeriodicThreeDM)
    (values : problem.GraphOrientation) (color : WireColor)
    (atom : Nat) (cell : Cell) :
    (problem.graphIncidentValues values color atom cell).length =
      problem.degree color atom := by
  simp [graphIncidentValues, degree]

/-- The degree promise supplies the only two shapes recognized by the
post-contraction local constraint. -/
theorem graphIncidentValues_length_two_or_three
    (problem : PeriodicThreeDM)
    (degree : problem.DegreeTwoOrThree)
    (values : problem.GraphOrientation) (color : WireColor)
    (atom : Nat) (atomLt : atom < problem.elementCount color)
    (cell : Cell) :
    (problem.graphIncidentValues values color atom cell).length = 2 ∨
      (problem.graphIncidentValues values color atom cell).length = 3 := by
  rw [graphIncidentValues_length]
  simpa using degree color atom atomLt

/-- Suppressing every degree-two colored vertex preserves the full local
orientation predicate. -/
theorem isGraphOrientation_iff_isSuppressedOrientation
    (problem : PeriodicThreeDM)
    (degree : problem.DegreeTwoOrThree)
    (values : problem.GraphOrientation) :
    problem.IsGraphOrientation values ↔
      problem.IsSuppressedOrientation values := by
  constructor
  · rintro ⟨tripleCoherent, covers⟩
    refine ⟨tripleCoherent, ?_⟩
    intro color atom atomLt cell
    exact
      (exactlyOne_iff_suppressedElementConstraint
        (problem.graphIncidentValues values color atom cell)
        (graphIncidentValues_length_two_or_three
          problem degree values color atom atomLt cell)).mp
        (covers color atom atomLt cell)
  · rintro ⟨tripleCoherent, covers⟩
    refine ⟨tripleCoherent, ?_⟩
    intro color atom atomLt cell
    exact
      (exactlyOne_iff_suppressedElementConstraint
        (problem.graphIncidentValues values color atom cell)
        (graphIncidentValues_length_two_or_three
          problem degree values color atom atomLt cell)).mpr
        (covers color atom atomLt cell)

/-- Contracting all degree-two colored vertices preserves existence of a
valid orientation. -/
theorem graphHasOrientation_iff_hasSuppressedOrientation
    (problem : PeriodicThreeDM)
    (degree : problem.DegreeTwoOrThree) :
    problem.GraphHasOrientation ↔
      problem.HasSuppressedOrientation := by
  constructor <;> rintro ⟨values, valid⟩
  · exact ⟨values,
      (isGraphOrientation_iff_isSuppressedOrientation
        problem degree values).mp valid⟩
  · exact ⟨values,
      (isGraphOrientation_iff_isSuppressedOrientation
        problem degree values).mpr valid⟩

/-- Perfect periodic 3D matchings are exactly orientations of the incidence
graph after its degree-two colored vertices have been suppressed. -/
theorem satisfiable_iff_hasSuppressedOrientation
    (problem : PeriodicThreeDM)
    (degree : problem.DegreeTwoOrThree) :
    problem.Satisfiable ↔ problem.HasSuppressedOrientation := by
  rw [problem.satisfiable_iff_graphHasOrientation,
    problem.graphHasOrientation_iff_hasSuppressedOrientation degree]

end PeriodicThreeDM

end LeanTrominoes
