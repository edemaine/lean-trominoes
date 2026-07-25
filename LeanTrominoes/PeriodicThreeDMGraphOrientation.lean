import LeanTrominoes.PeriodicThreeDMGraph

/-!
# Orientations of the periodic 3DM incidence graph

An `IncidenceTag` names one colored edge orbit of the incidence graph.
Consequently an edge orientation is a Boolean for every tag and lattice
translate, where `true` means that the edge points from its triple endpoint
toward its colored-element endpoint.

This file restates the 3DM orientation constraints directly on those graph
edge tags and proves that the tagged and curried presentations are equivalent.
Together with `PeriodicThreeDM.satisfiable_iff_hasOrientation`, this is the
semantic bridge from perfect matching to the graph consumed by the drawing
reduction.
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- One direction value for every lifted edge of the incidence graph. -/
abbrev GraphOrientation (_problem : PeriodicThreeDM) :=
  IncidenceTag → Cell → Bool

/-- Read the tagged graph-edge values incident to one translated element. -/
def graphIncidentValues (problem : PeriodicThreeDM)
    (values : problem.GraphOrientation) (color : WireColor)
    (atom : Nat) (cell : Cell) : List Bool :=
  (problem.incidences color atom).map fun incidence =>
    values ⟨incidence.tripleIndex, color⟩
      (Cell.sub cell incidence.offset)

/-- Every translated colored element has exactly one incoming tagged edge. -/
def GraphCoversElements (problem : PeriodicThreeDM)
    (values : problem.GraphOrientation) : Prop :=
  ∀ color atom, atom < problem.elementCount color → ∀ cell,
    PeriodicOneInThree.ExactlyOne
      (problem.graphIncidentValues values color atom cell)

/-- At every translated triple vertex, its red, green, and blue tagged edges
are directed coherently. -/
def GraphTripleCoherent (problem : PeriodicThreeDM)
    (values : problem.GraphOrientation) : Prop :=
  ∀ tripleIndex, tripleIndex < problem.triples.length → ∀ cell,
    values ⟨tripleIndex, .red⟩ cell =
        values ⟨tripleIndex, .green⟩ cell ∧
      values ⟨tripleIndex, .green⟩ cell =
        values ⟨tripleIndex, .blue⟩ cell

/-- The local 1-in-3 and 0-or-3 constraints on the tagged incidence graph. -/
def IsGraphOrientation (problem : PeriodicThreeDM)
    (values : problem.GraphOrientation) : Prop :=
  problem.GraphTripleCoherent values ∧
    problem.GraphCoversElements values

/-- The periodic 3DM incidence graph admits a valid tagged orientation. -/
def GraphHasOrientation (problem : PeriodicThreeDM) : Prop :=
  ∃ values, problem.IsGraphOrientation values

/-- Curry a tagged graph orientation into the original triple/color form. -/
def fromGraphOrientation (problem : PeriodicThreeDM)
    (values : problem.GraphOrientation) : problem.Orientation :=
  fun tripleIndex cell color =>
    values ⟨tripleIndex, color⟩ cell

/-- Attach an incidence tag to a triple/color orientation value. -/
def toGraphOrientation (problem : PeriodicThreeDM)
    (orientation : problem.Orientation) : problem.GraphOrientation :=
  fun tag cell =>
    orientation tag.tripleIndex cell tag.color

@[simp]
theorem fromGraphOrientation_toGraphOrientation
    (problem : PeriodicThreeDM)
    (orientation : problem.Orientation) :
    problem.fromGraphOrientation
        (problem.toGraphOrientation orientation) =
      orientation := by
  rfl

@[simp]
theorem toGraphOrientation_fromGraphOrientation
    (problem : PeriodicThreeDM)
    (values : problem.GraphOrientation) :
    problem.toGraphOrientation
        (problem.fromGraphOrientation values) =
      values := by
  funext tag cell
  rcases tag with ⟨tripleIndex, color⟩
  rfl

@[simp]
theorem graphIncidentValues_toGraphOrientation
    (problem : PeriodicThreeDM)
    (orientation : problem.Orientation)
    (color : WireColor) (atom : Nat) (cell : Cell) :
    problem.graphIncidentValues
        (problem.toGraphOrientation orientation) color atom cell =
      problem.incidentValues orientation color atom cell := by
  rfl

@[simp]
theorem graphTripleCoherent_toGraphOrientation_iff
    (problem : PeriodicThreeDM)
    (orientation : problem.Orientation) :
    problem.GraphTripleCoherent
        (problem.toGraphOrientation orientation) ↔
      problem.TripleCoherent orientation := by
  rfl

@[simp]
theorem graphCoversElements_toGraphOrientation_iff
    (problem : PeriodicThreeDM)
    (orientation : problem.Orientation) :
    problem.GraphCoversElements
        (problem.toGraphOrientation orientation) ↔
      problem.CoversElements orientation := by
  rfl

@[simp]
theorem isGraphOrientation_toGraphOrientation_iff
    (problem : PeriodicThreeDM)
    (orientation : problem.Orientation) :
    problem.IsGraphOrientation
        (problem.toGraphOrientation orientation) ↔
      problem.IsOrientation orientation := by
  rfl

@[simp]
theorem isOrientation_fromGraphOrientation_iff
    (problem : PeriodicThreeDM)
    (values : problem.GraphOrientation) :
    problem.IsOrientation
        (problem.fromGraphOrientation values) ↔
      problem.IsGraphOrientation values := by
  rfl

/-- The tagged edge-orbit presentation and the original triple/color
presentation admit orientations simultaneously. -/
theorem graphHasOrientation_iff_hasOrientation
    (problem : PeriodicThreeDM) :
    problem.GraphHasOrientation ↔ problem.HasOrientation := by
  constructor
  · rintro ⟨values, valid⟩
    exact ⟨problem.fromGraphOrientation values,
      (isOrientation_fromGraphOrientation_iff problem values).2 valid⟩
  · rintro ⟨orientation, valid⟩
    exact ⟨problem.toGraphOrientation orientation,
      (isGraphOrientation_toGraphOrientation_iff
        problem orientation).2 valid⟩

/-- Perfect periodic 3D matchings are exactly valid orientations of the
tagged periodic incidence graph. -/
theorem satisfiable_iff_graphHasOrientation
    (problem : PeriodicThreeDM) :
    problem.Satisfiable ↔ problem.GraphHasOrientation := by
  rw [graphHasOrientation_iff_hasOrientation,
    satisfiable_iff_hasOrientation]

end PeriodicThreeDM
end LeanTrominoes
