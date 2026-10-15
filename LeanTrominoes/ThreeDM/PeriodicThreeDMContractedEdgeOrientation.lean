/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Orientation.Normalization.PeriodicThreeDMNormalizationReverseElementOrientation
import Lean.Util.CollectAxioms

/-! # One direction bit per contracted colored edge

Unlike an incidence assignment, an edge assignment automatically gives
opposite inward values at its two endpoints. Suppressing degree-two elements
preserves orientability in this actual edge representation.
-/
namespace LeanTrominoes.PeriodicThreeDM
open Gadget
set_option maxHeartbeats 800000

abbrev ContractedEdgeOrientation := ContractedEdge → Cell → Bool

def ContractedEndpoint.edgeInward (a : ContractedEdgeOrientation) :
    ContractedEndpoint → Cell → Bool
  | .source edge, cell => !(a edge cell)
  | .target edge, cell => a edge (Cell.sub cell edge.toPeriodicEdge.offset)

def IsContractedEdgeOrientation (problem : PeriodicThreeDM)
    (a : ContractedEdgeOrientation) : Prop :=
  (∀ index, index < problem.triples.length → ∀ cell,
    ∀ first ∈ problem.contractedEndpointsAt (.triple index),
    ∀ second ∈ problem.contractedEndpointsAt (.triple index),
      first.edgeInward a cell = second.edgeInward a cell) ∧
  (∀ color atom, atom < problem.elementCount color → problem.degree color atom = 3 →
    ∀ cell, PeriodicOneInThree.ExactlyOne
      ((problem.contractedEndpointsAt (.element color atom)).map
        fun endpoint => endpoint.edgeInward a cell))

def HasContractedEdgeOrientation (problem : PeriodicThreeDM) : Prop :=
  ∃ a, problem.IsContractedEdgeOrientation a

def toContractedEdgeOrientation (values : IncidenceTag → Cell → Bool) :
    ContractedEdgeOrientation := fun edge cell => values edge.sourceTag cell

def fromContractedEdgeOrientation (problem : PeriodicThreeDM)
    (a : ContractedEdgeOrientation) : problem.GraphOrientation :=
  fun tag cell => !((problem.contractedTripleEndpointForTag tag).edgeInward a cell)

private theorem emitted_end_opposite (problem : PeriodicThreeDM)
    (values : problem.GraphOrientation) (valid : problem.IsSuppressedOrientation values)
    {edge : ContractedEdge} (member : edge ∈ problem.contractedEdges) (cell : Cell) :
    edge.sourceInward values cell ≠ edge.targetInward values cell := by
  rcases List.mem_flatMap.mp member with ⟨color, _, member⟩
  rcases List.mem_flatMap.mp member with ⟨atom, atomMember, member⟩
  exact contractedEdge_endpointInward_ne_of_mem problem values valid color atom
    (List.mem_range.mp atomMember) member cell

theorem edgeInward_to_at_triple (problem : PeriodicThreeDM)
    (values : problem.GraphOrientation) (valid : problem.IsSuppressedOrientation values)
    {endpoint : ContractedEndpoint} (member : endpoint ∈ problem.contractedEndpoints)
    (index : Nat) (vertex : endpoint.vertex = .triple index) (cell : Cell) :
    endpoint.edgeInward (toContractedEdgeOrientation values) cell =
      !(values ⟨index,endpoint.color⟩ cell) := by
  have edgeMember := endpoint.edge_mem_of_mem member
  cases endpoint with
  | source edge =>
      cases edge <;> simp_all [ContractedEndpoint.vertex,ContractedEdge.toPeriodicEdge,
        ContractedEndpoint.edgeInward,toContractedEdgeOrientation,
        ContractedEdge.sourceTag,ContractedEndpoint.color]
  | target edge =>
      cases edge with
      | retained color atom incidence =>
          simp [ContractedEndpoint.vertex,ContractedEdge.toPeriodicEdge] at vertex
      | through color atom first second =>
          simp only [ContractedEndpoint.vertex,ContractedEdge.toPeriodicEdge,
            PeriodicThreeDMVertex.triple.injEq] at vertex
          subst index
          have different := emitted_end_opposite problem values valid edgeMember
            (Cell.sub cell (Cell.sub first.offset second.offset))
          simp only [ContractedEndpoint.edge,ContractedEdge.sourceInward,ContractedEdge.sourceTag,
            ContractedEdge.targetInward,Cell.add_sub_right_cancel] at different
          simpa [ContractedEndpoint.edgeInward,toContractedEdgeOrientation,
            ContractedEdge.toPeriodicEdge,ContractedEdge.sourceTag,ContractedEndpoint.color,
            ContractedEndpoint.edge] using (bool_eq_not_of_ne _ _ (Ne.symm different)).symm

private theorem colors_coherent (problem : PeriodicThreeDM)
    (values : problem.GraphOrientation) (valid : problem.IsSuppressedOrientation values)
    (index : Nat) (bound : index < problem.triples.length) (cell : Cell)
    (first second : WireColor) : values ⟨index,first⟩ cell = values ⟨index,second⟩ cell := by
  have h := valid.1 index bound cell
  cases first <;> cases second <;> simp_all

theorem toContractedEdgeOrientation_valid (problem : PeriodicThreeDM)
    (degree : problem.DegreeTwoOrThree) (values : problem.GraphOrientation)
    (valid : problem.IsSuppressedOrientation values) :
    problem.IsContractedEdgeOrientation (toContractedEdgeOrientation values) := by
  constructor
  · intro index bound cell first firstMember second secondMember
    rcases (problem.contractedEndpointsAt_mem_iff _ _).mp firstMember with ⟨firstListed,firstVertex⟩
    rcases (problem.contractedEndpointsAt_mem_iff _ _).mp secondMember with ⟨secondListed,secondVertex⟩
    rw [edgeInward_to_at_triple problem values valid firstListed index firstVertex cell,
      edgeInward_to_at_triple problem values valid secondListed index secondVertex cell,
      colors_coherent problem values valid index bound cell first.color second.color]
  · intro color atom bound degreeThree cell
    obtain ⟨first,second,third,incidences⟩ := exists_eq_triple_of_length_eq_three
      (problem.incidences color atom) degreeThree
    have perm := (contractedEdgesForElement_targets_perm_endpointsAt problem degree
      color atom bound degreeThree).map (fun endpoint =>
        endpoint.edgeInward (toContractedEdgeOrientation values) cell)
    change _ = 1
    rw [← perm.count_eq]
    simpa [List.map_map,ContractedEndpoint.edgeInward,toContractedEdgeOrientation,
      contractedEdgesForElement,incidences,ContractedEdge.toPeriodicEdge,
      ContractedEdge.sourceTag,retainedElementInwardValues,
      ContractedEdge.targetInwardAtTarget,ContractedEdge.targetInward,PeriodicOneInThree.ExactlyOne] using
      retainedElementInwardValues_exactlyOne problem values valid color atom bound
        first second third incidences cell

theorem fromContractedEdgeOrientation_source (problem : PeriodicThreeDM)
    (wellFormed : problem.IsWellFormed) (degree : problem.DegreeTwoOrThree)
    (a : ContractedEdgeOrientation) {edge : ContractedEdge}
    (member : edge ∈ problem.contractedEdges) (cell : Cell) :
    problem.fromContractedEdgeOrientation a edge.sourceTag cell = a edge cell := by
  simp [fromContractedEdgeOrientation,
    problem.contractedTripleEndpointForTag_sourceTag wellFormed degree member,
    ContractedEndpoint.edgeInward]

theorem fromContractedEdgeOrientation_through_target (problem : PeriodicThreeDM)
    (wellFormed : problem.IsWellFormed) (degree : problem.DegreeTwoOrThree)
    (a : ContractedEdgeOrientation) (color : WireColor) (atom : Nat)
    (first second : Incidence)
    (member : ContractedEdge.through color atom first second ∈ problem.contractedEdges)
    (cell : Cell) :
    problem.fromContractedEdgeOrientation a
      (ContractedEdge.through color atom first second).targetTag cell =
      !(a (.through color atom first second)
        (Cell.sub cell (Cell.sub first.offset second.offset))) := by
  simp [fromContractedEdgeOrientation,
    problem.contractedTripleEndpointForTag_through_targetTag wellFormed degree
      color atom first second member,ContractedEndpoint.edgeInward,
    ContractedEdge.toPeriodicEdge]

private theorem selected_at_triple (problem : PeriodicThreeDM)
    (wellFormed : problem.IsWellFormed) (degree : problem.DegreeTwoOrThree)
    (index : Nat) (bound : index < problem.triples.length) (color : WireColor) :
    problem.contractedTripleEndpointForTag ⟨index,color⟩ ∈
      problem.contractedEndpointsAt (.triple index) := by
  have tagMember := tripleIncidenceTag_mem_incidenceTags problem index bound color
  apply (problem.contractedEndpointsAt_mem_iff _ _).mpr
  exact ⟨contractedTripleEndpoint_mem_contractedEndpoints problem
    (problem.contractedTripleEndpointForTag_mem wellFormed degree tagMember),
    problem.contractedTripleEndpointForTag_vertex wellFormed degree tagMember⟩

theorem fromContractedEdgeOrientation_valid (problem : PeriodicThreeDM)
    (wellFormed : problem.IsWellFormed) (degree : problem.DegreeTwoOrThree)
    (a : ContractedEdgeOrientation) (valid : problem.IsContractedEdgeOrientation a) :
    problem.IsSuppressedOrientation (problem.fromContractedEdgeOrientation a) := by
  constructor
  · intro index bound cell
    constructor <;> apply congrArg (fun b : Bool => !b)
    · exact valid.1 index bound cell _ (selected_at_triple problem wellFormed degree index bound .red)
        _ (selected_at_triple problem wellFormed degree index bound .green)
    · exact valid.1 index bound cell _ (selected_at_triple problem wellFormed degree index bound .green)
        _ (selected_at_triple problem wellFormed degree index bound .blue)
  · intro color atom bound cell
    have degreeCases := degree color atom bound
    simp only [List.mem_cons,List.not_mem_nil,or_false] at degreeCases
    rcases degreeCases with degreeTwo | degreeThree
    · obtain ⟨first,second,incidences⟩ :
          ∃ first second, problem.incidences color atom = [first,second] := by
        have length : (problem.incidences color atom).length = 2 := degreeTwo
        generalize problem.incidences color atom = xs at length ⊢
        rcases xs with _ | ⟨first,xs⟩; · simp at length
        rcases xs with _ | ⟨second,xs⟩; · simp at length
        rcases xs with _ | ⟨third,xs⟩; · exact ⟨first,second,rfl⟩
        simp at length
      have localMember : ContractedEdge.through color atom first second ∈
          problem.contractedEdgesForElement color atom := by
        simp [contractedEdgesForElement,incidences]
      have member := contractedEdgesForElement_mem_contractedEdges problem color atom bound localMember
      rw [graphIncidentValues,incidences]
      simp only [List.map_cons,List.map_nil,suppressedElementConstraint_pair_iff]
      rw [← show (ContractedEdge.through color atom first second).sourceTag =
        (⟨first.tripleIndex,color⟩ : IncidenceTag) from rfl,
        ← show (ContractedEdge.through color atom first second).targetTag =
        (⟨second.tripleIndex,color⟩ : IncidenceTag) from rfl,
        fromContractedEdgeOrientation_source problem wellFormed degree a member,
        fromContractedEdgeOrientation_through_target problem wellFormed degree a color atom first second member]
      have cells : Cell.sub (Cell.sub cell second.offset) (Cell.sub first.offset second.offset) =
          Cell.sub cell first.offset := by
        rcases cell with ⟨x,y⟩; rcases first with ⟨_,fx,fy⟩; rcases second with ⟨_,sx,sy⟩
        simp [Cell.sub]
      rw [cells]
      cases a (.through color atom first second) (Cell.sub cell first.offset) <;> decide
    · obtain ⟨first,second,third,incidences⟩ := exists_eq_triple_of_length_eq_three
        (problem.incidences color atom) degreeThree
      have endpointOne := valid.2 color atom bound degreeThree cell
      have perm := (contractedEdgesForElement_targets_perm_endpointsAt problem degree
        color atom bound degreeThree).map (fun endpoint => endpoint.edgeInward a cell)
      have localEquality :
          (problem.contractedEdgesForElement color atom).map (fun edge =>
            edge.targetInwardAtTarget (problem.fromContractedEdgeOrientation a) cell) =
          (problem.contractedEdgesForElement color atom).map (fun edge =>
            (ContractedEndpoint.target edge).edgeInward a cell) := by
        apply List.map_congr_left
        intro edge edgeMember
        have member := contractedEdgesForElement_mem_contractedEdges problem color atom bound edgeMember
        simp only [contractedEdgesForElement,incidences,List.mem_cons,List.not_mem_nil,or_false] at edgeMember
        rcases edgeMember with rfl | rfl | rfl <;>
          exact fromContractedEdgeOrientation_source problem wellFormed degree a member _
      have lengthThree := problem.graphIncidentValues_length_two_or_three degree
        (problem.fromContractedEdgeOrientation a) color atom bound cell
      apply (exactlyOne_iff_suppressedElementConstraint _ lengthThree).mp
      rw [← retainedElementInwardValues_eq_graphIncidentValues problem
        (problem.fromContractedEdgeOrientation a) color atom first second third incidences]
      change _ = 1
      rw [retainedElementInwardValues,localEquality]
      change _ = 1 at endpointOne
      simpa [List.map_map,Function.comp_def] using perm.count_eq true |>.trans endpointOne

theorem hasContractedEdgeOrientation_iff_satisfiable (problem : PeriodicThreeDM)
    (wellFormed : problem.IsWellFormed) (degree : problem.DegreeTwoOrThree) :
    problem.HasContractedEdgeOrientation ↔ problem.Satisfiable := by
  rw [problem.satisfiable_iff_hasSuppressedOrientation degree]
  constructor
  · rintro ⟨a,valid⟩
    exact ⟨problem.fromContractedEdgeOrientation a,
      fromContractedEdgeOrientation_valid problem wellFormed degree a valid⟩
  · rintro ⟨values,valid⟩
    exact ⟨toContractedEdgeOrientation values,
      toContractedEdgeOrientation_valid problem degree values valid⟩

open Lean Elab Command in
run_cmd do
  let name := ``hasContractedEdgeOrientation_iff_satisfiable
  let axioms ← Lean.collectAxioms name
  let extra := axioms.filter fun ax =>
    ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
  unless extra.isEmpty do throwError "{name} depends on unexpected axioms: {extra}"

end LeanTrominoes.PeriodicThreeDM
