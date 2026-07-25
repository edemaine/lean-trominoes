import LeanTrominoes.PeriodicThreeDMContraction

/-!
# Orientations at the endpoints of contracted periodic 3DM edges

An original 3DM incidence value is `true` when it points from its triple
toward its colored element.  This file transports those values to the actual
endpoints of the executable contracted graph.

At a triple endpoint the inward value is therefore the negation of the
original incidence value.  At a retained colored endpoint it is the original
value.  At the second triple endpoint of a through edge it is again the
negation, evaluated at the translated target triple.  The degree-two
suppressed-element constraint says exactly that the two endpoint-inward
values of a through edge are opposite.
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM
namespace ContractedEdge

/-- Inward orientation value at the source triple of a contracted edge based
at the supplied source translate. -/
def sourceInward (values : IncidenceTag → Cell → Bool)
    (edge : ContractedEdge) (sourceCell : Cell) : Bool :=
  !(values edge.sourceTag sourceCell)

/-- Inward orientation value at the target of a contracted edge based at the
supplied source translate.  A retained target is a colored element; a through
target is the second triple at the contracted edge's translated endpoint. -/
def targetInward (values : IncidenceTag → Cell → Bool) :
    (edge : ContractedEdge) → Cell → Bool
  | .retained color _atom incidence, sourceCell =>
      values ⟨incidence.tripleIndex, color⟩ sourceCell
  | .through color _atom first second, sourceCell =>
      !(values ⟨second.tripleIndex, color⟩
        (Cell.add sourceCell (Cell.sub first.offset second.offset)))

/-- Read the target-inward value using the target translate rather than the
source translate. -/
def targetInwardAtTarget (values : IncidenceTag → Cell → Bool)
    (edge : ContractedEdge) (targetCell : Cell) : Bool :=
  edge.targetInward values
    (Cell.sub targetCell edge.toPeriodicEdge.offset)

@[simp]
theorem sourceInward_retained
    (values : IncidenceTag → Cell → Bool)
    (color : WireColor) (atom : Nat) (incidence : Incidence)
    (sourceCell : Cell) :
    (ContractedEdge.retained color atom incidence).sourceInward
        values sourceCell =
      !(values ⟨incidence.tripleIndex, color⟩ sourceCell) := by
  rfl

@[simp]
theorem sourceInward_through
    (values : IncidenceTag → Cell → Bool)
    (color : WireColor) (atom : Nat) (first second : Incidence)
    (sourceCell : Cell) :
    (ContractedEdge.through color atom first second).sourceInward
        values sourceCell =
      !(values ⟨first.tripleIndex, color⟩ sourceCell) := by
  rfl

@[simp]
theorem targetInward_retained
    (values : IncidenceTag → Cell → Bool)
    (color : WireColor) (atom : Nat) (incidence : Incidence)
    (sourceCell : Cell) :
    (ContractedEdge.retained color atom incidence).targetInward
        values sourceCell =
      values ⟨incidence.tripleIndex, color⟩ sourceCell := by
  rfl

@[simp]
theorem targetInward_through
    (values : IncidenceTag → Cell → Bool)
    (color : WireColor) (atom : Nat) (first second : Incidence)
    (sourceCell : Cell) :
    (ContractedEdge.through color atom first second).targetInward
        values sourceCell =
      !(values ⟨second.tripleIndex, color⟩
        (Cell.add sourceCell
          (Cell.sub first.offset second.offset))) := by
  rfl

/-- The source and target inward values of a retained incidence edge are
opposite by construction. -/
theorem retained_endpointInward_ne
    (values : IncidenceTag → Cell → Bool)
    (color : WireColor) (atom : Nat) (incidence : Incidence)
    (sourceCell : Cell) :
    (ContractedEdge.retained color atom incidence).sourceInward
        values sourceCell ≠
      (ContractedEdge.retained color atom incidence).targetInward
        values sourceCell := by
  simp only [sourceInward_retained, targetInward_retained]
  cases values ⟨incidence.tripleIndex, color⟩ sourceCell <;> decide

end ContractedEdge

/-- Subtracting the first incidence offset from its translated element cell
recovers the source triple translate. -/
@[simp]
theorem sub_add_incidence_offset (cell offset : Cell) :
    Cell.sub (Cell.add cell offset) offset = cell := by
  rcases cell with ⟨cellX, cellY⟩
  rcases offset with ⟨offsetX, offsetY⟩
  simp [Cell.sub, Cell.add]

/-- The same element cell, viewed through the second incidence, is the
translated target triple of a through edge. -/
theorem sub_add_first_offset_second
    (cell firstOffset secondOffset : Cell) :
    Cell.sub (Cell.add cell firstOffset) secondOffset =
      Cell.add cell (Cell.sub firstOffset secondOffset) := by
  rcases cell with ⟨cellX, cellY⟩
  rcases firstOffset with ⟨firstX, firstY⟩
  rcases secondOffset with ⟨secondX, secondY⟩
  simp [Cell.sub, Cell.add]
  constructor <;> omega

/-- A valid suppressed orientation gives opposite inward values at the two
triple endpoints of the edge replacing one degree-two colored element. -/
theorem through_endpointInward_ne
    (problem : PeriodicThreeDM)
    (values : problem.GraphOrientation)
    (valid : problem.IsSuppressedOrientation values)
    (color : WireColor) (atom : Nat)
    (atomLt : atom < problem.elementCount color)
    (first second : Incidence)
    (incidences :
      problem.incidences color atom = [first, second])
    (sourceCell : Cell) :
    (ContractedEdge.through color atom first second).sourceInward
        values sourceCell ≠
      (ContractedEdge.through color atom first second).targetInward
        values sourceCell := by
  have constraint :=
    valid.2 color atom atomLt (Cell.add sourceCell first.offset)
  rw [graphIncidentValues, incidences] at constraint
  simp only [List.map_cons, List.map_nil,
    suppressedElementConstraint_pair_iff] at constraint
  rw [sub_add_incidence_offset,
    sub_add_first_offset_second] at constraint
  simp only [ContractedEdge.sourceInward_through,
    ContractedEdge.targetInward_through]
  intro inwardEqual
  apply constraint
  cases firstValue :
      values ⟨first.tripleIndex, color⟩ sourceCell <;>
    cases secondValue :
      values ⟨second.tripleIndex, color⟩
        (Cell.add sourceCell
          (Cell.sub first.offset second.offset)) <;>
    simp_all

/-- Every executable edge emitted for a colored element has opposite inward
values at its actual source and target lifts. -/
theorem contractedEdge_endpointInward_ne_of_mem
    (problem : PeriodicThreeDM)
    (values : problem.GraphOrientation)
    (valid : problem.IsSuppressedOrientation values)
    (color : WireColor) (atom : Nat)
    (atomLt : atom < problem.elementCount color)
    {edge : ContractedEdge}
    (member :
      edge ∈ problem.contractedEdgesForElement color atom)
    (sourceCell : Cell) :
    edge.sourceInward values sourceCell ≠
      edge.targetInward values sourceCell := by
  unfold contractedEdgesForElement at member
  generalize incidencesEq :
      problem.incidences color atom = incidences at member
  rcases incidences with _ | ⟨first, incidences⟩
  · simp at member
  rcases incidences with _ | ⟨second, incidences⟩
  · simp at member
  rcases incidences with _ | ⟨third, incidences⟩
  · simp only [List.mem_singleton] at member
    subst edge
    exact through_endpointInward_ne problem values valid color atom
      atomLt first second incidencesEq sourceCell
  rcases incidences with _ | ⟨fourth, incidences⟩
  · simp at member
    rcases member with rfl | rfl | rfl <;>
      exact ContractedEdge.retained_endpointInward_ne
        values color atom _ sourceCell
  simp at member

/-- Target-inward values of all edges retained at one colored element,
evaluated at that element's translate. -/
def retainedElementInwardValues
    (problem : PeriodicThreeDM)
    (values : problem.GraphOrientation)
    (color : WireColor) (atom : Nat) (elementCell : Cell) : List Bool :=
  (problem.contractedEdgesForElement color atom).map fun edge =>
    edge.targetInwardAtTarget values elementCell

/-- For a degree-three element, the executable retained-edge endpoint values
are exactly the original incidence values at that translated element. -/
theorem retainedElementInwardValues_eq_graphIncidentValues
    (problem : PeriodicThreeDM)
    (values : problem.GraphOrientation)
    (color : WireColor) (atom : Nat)
    (first second third : Incidence)
    (incidences :
      problem.incidences color atom = [first, second, third])
    (elementCell : Cell) :
    problem.retainedElementInwardValues values color atom elementCell =
      problem.graphIncidentValues values color atom elementCell := by
  rw [graphIncidentValues, incidences]
  simp [retainedElementInwardValues, contractedEdgesForElement,
    incidences, ContractedEdge.targetInwardAtTarget,
    ContractedEdge.targetInward, ContractedEdge.toPeriodicEdge]

/-- The three actual retained-edge endpoints at a degree-three colored
element satisfy the monochromatic exact-one constraint. -/
theorem retainedElementInwardValues_exactlyOne
    (problem : PeriodicThreeDM)
    (values : problem.GraphOrientation)
    (valid : problem.IsSuppressedOrientation values)
    (color : WireColor) (atom : Nat)
    (atomLt : atom < problem.elementCount color)
    (first second third : Incidence)
    (incidences :
      problem.incidences color atom = [first, second, third])
    (elementCell : Cell) :
    PeriodicOneInThree.ExactlyOne
      (problem.retainedElementInwardValues
        values color atom elementCell) := by
  rw [retainedElementInwardValues_eq_graphIncidentValues
    problem values color atom first second third incidences]
  have constraint := valid.2 color atom atomLt elementCell
  rw [graphIncidentValues, incidences]
  rw [graphIncidentValues, incidences] at constraint
  simpa only [List.map_cons, List.map_nil,
    suppressedElementConstraint_triple_iff] using constraint

/-- Negating the original three incidence values gives coherent inward
values at every actual trichromatic triple vertex. -/
theorem tripleInward_coherent
    (problem : PeriodicThreeDM)
    (values : problem.GraphOrientation)
    (valid : problem.IsSuppressedOrientation values)
    (tripleIndex : Nat)
    (indexLt : tripleIndex < problem.triples.length)
    (cell : Cell) :
    (!(values ⟨tripleIndex, .red⟩ cell)) =
        (!(values ⟨tripleIndex, .green⟩ cell)) ∧
      (!(values ⟨tripleIndex, .green⟩ cell)) =
        (!(values ⟨tripleIndex, .blue⟩ cell)) := by
  have coherent := valid.1 tripleIndex indexLt cell
  exact
    ⟨congrArg (fun value : Bool => !value) coherent.1,
      congrArg (fun value : Bool => !value) coherent.2⟩

end PeriodicThreeDM
end LeanTrominoes
