/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Orientation.Normalization.PeriodicThreeDMGraphOrientationEncoding
import Lean.Util.CollectAxioms

/-! # Correctness of the general graph orientation encoding -/
namespace LeanTrominoes.PeriodicThreeDM.GraphOrientationEncoding
open Gadget TrichromaticGraphOrientation
set_option maxHeartbeats 1000000

theorem kind_at (problem : PeriodicThreeDM) {vertex : PeriodicThreeDMVertex}
    (member : vertex ∈ problem.contractedGraph.vertices) :
    (input problem).1.getD (problem.contractedGraph.vertices.idxOf vertex) false = vertexKind vertex := by
  simp [input,List.getD,List.getElem?_map,List.getElem?_idxOf member]

theorem triple_mem (problem : PeriodicThreeDM) (index : Nat) :
    PeriodicThreeDMVertex.triple index ∈ problem.contractedGraph.vertices ↔
      index < problem.triples.length := by
  simp [contractedGraph,tripleVertices,contractedElementVertices,
    contractedElementVerticesForColor,incidenceColors]

theorem element_mem (problem : PeriodicThreeDM) (color : WireColor) (atom : Nat) :
    PeriodicThreeDMVertex.element color atom ∈ problem.contractedGraph.vertices ↔
      atom < problem.elementCount color ∧ problem.degree color atom = 3 := by
  cases color <;> simp [contractedGraph,tripleVertices,contractedElementVertices,
    contractedElementVerticesForColor,incidenceColors,elementCount]

private theorem triple_colors_nodup (problem : PeriodicThreeDM) (degree : problem.DegreeTwoOrThree)
    (index : Nat) :
    ((problem.contractedEndpointsAt (.triple index)).map ContractedEndpoint.color).Nodup := by
  apply List.Nodup.map_on
  · intro first firstMember second secondMember same
    rcases (problem.contractedEndpointsAt_mem_iff _ _).mp firstMember with ⟨firstListed,firstVertex⟩
    rcases (problem.contractedEndpointsAt_mem_iff _ _).mp secondMember with ⟨secondListed,secondVertex⟩
    by_contra different
    exact (ContractedEndpoint.color_ne_of_vertex_eq_triple degree firstListed secondListed
      different index firstVertex secondVertex) same
  · exact contractedEndpointsAt_nodup problem degree _

private theorem rainbow_count (xs : List WireColor) (length : xs.length = 3) (nodup : xs.Nodup) :
    ∀ color : WireColor, xs.count color = 1 := by
  obtain ⟨first,second,third,rfl⟩ := exists_eq_triple_of_length_eq_three xs length
  intro color
  cases first <;> cases second <;> cases third <;> cases color <;> simp_all

theorem input_wellFormed (problem : PeriodicThreeDM) (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree) : TrichromaticGraphOrientation.IsWellFormed (input problem) := by
  constructor
  · intro record member
    rcases List.mem_map.mp member with ⟨edge,edgeMember,rfl⟩
    have endsMember := (contractedGraph_isWellFormed problem).2 edge.toPeriodicEdge
      (List.mem_map.mpr ⟨edge,edgeMember,rfl⟩)
    simpa [input,edgeRecord] using
      And.intro (List.idxOf_lt_length_iff.mpr endsMember.1)
        (List.idxOf_lt_length_iff.mpr endsMember.2)
  · intro index bound
    have bound' : index < problem.contractedGraph.vertices.length := by simpa [input] using bound
    let vertex := problem.contractedGraph.vertices[index]'bound'
    have member : vertex ∈ problem.contractedGraph.vertices := List.getElem_mem bound'
    have indexEq : problem.contractedGraph.vertices.idxOf vertex = index :=
      (contractedGraph_vertices_nodup problem).idxOf_getElem index bound'
    rw [← indexEq,kind_at problem member,colors_eq problem degree]
    cases vertexEq : vertex with
    | triple tripleIndex =>
        rw [vertexEq] at member
        have tripleBound := (triple_mem problem tripleIndex).mp member
        have length := contractedEndpointsAt_triple_length problem wellFormed degree tripleIndex tripleBound
        refine ⟨by simpa using length,?_⟩
        exact rainbow_count _ (by simpa using length) (triple_colors_nodup problem degree tripleIndex)
    | element color atom =>
        rw [vertexEq] at member
        rcases (element_mem problem color atom).mp member with ⟨atomBound,degreeThree⟩
        refine ⟨by simpa using contractedEndpointsAt_element_length problem color atom atomBound degreeThree,?_⟩
        refine ⟨color,?_⟩
        intro c cMember
        rcases List.mem_map.mp cMember with ⟨endpoint,endpointMember,rfl⟩
        exact endpoint.color_eq_of_vertex_eq_element color atom
          ((problem.contractedEndpointsAt_mem_iff _ _).mp endpointMember).2

private theorem literal_holds_iff (problem : PeriodicThreeDM) (a : Nat → Cell → Bool)
    (cell : Cell) (endpoint : ContractedEndpoint) :
    (endpointLiteral problem endpoint).Holds a cell ↔
      endpoint.edgeInward (edgeAssignment problem a) cell = true := by
  rw [← literalValue_eq problem a cell endpoint]
  simp [PeriodicLiteral.Holds]

private theorem bool_iff (a b : Bool) : (a = true ↔ b = true) ↔ a = b := by
  cases a <;> cases b <;> decide

theorem coherent_iff (problem : PeriodicThreeDM) (degree : problem.DegreeTwoOrThree)
    (a : Nat → Cell → Bool) (cell : Cell) (vertex : PeriodicThreeDMVertex) :
    Coherent a cell (incoming (input problem) (problem.contractedGraph.vertices.idxOf vertex)) ↔
      ∀ first ∈ problem.contractedEndpointsAt vertex,
      ∀ second ∈ problem.contractedEndpointsAt vertex,
        first.edgeInward (edgeAssignment problem a) cell =
          second.edgeInward (edgeAssignment problem a) cell := by
  simp only [Coherent,incoming_eq problem degree,List.forall_mem_map]
  simp_rw [literal_holds_iff,bool_iff]

theorem orientation_iff (problem : PeriodicThreeDM) (degree : problem.DegreeTwoOrThree)
    (a : Nat → Cell → Bool) :
    TrichromaticGraphOrientation.IsOrientation (input problem) a ↔
      problem.IsContractedEdgeOrientation (edgeAssignment problem a) := by
  constructor
  · intro valid
    constructor
    · intro index bound cell
      have member := (triple_mem problem index).mpr bound
      have atVertex := valid cell (problem.contractedGraph.vertices.idxOf (.triple index))
        (by simpa [input] using List.idxOf_lt_length_iff.mpr member)
      rw [kind_at problem member] at atVertex
      exact (coherent_iff problem degree a cell (.triple index)).mp atVertex
    · intro color atom bound degreeThree cell
      have member := (element_mem problem color atom).mpr ⟨bound,degreeThree⟩
      have atVertex := valid cell (problem.contractedGraph.vertices.idxOf (.element color atom))
        (by simpa [input] using List.idxOf_lt_length_iff.mpr member)
      rw [kind_at problem member] at atVertex
      simpa [vertexKind,PeriodicOneInThree.ClauseHolds,clauseValues_eq problem degree] using atVertex
  · intro valid cell index bound
    have bound' : index < problem.contractedGraph.vertices.length := by simpa [input] using bound
    let vertex := problem.contractedGraph.vertices[index]'bound'
    have member : vertex ∈ problem.contractedGraph.vertices := List.getElem_mem bound'
    have indexEq : problem.contractedGraph.vertices.idxOf vertex = index :=
      (contractedGraph_vertices_nodup problem).idxOf_getElem index bound'
    rw [← indexEq,kind_at problem member]
    cases vertexEq : vertex with
    | triple tripleIndex =>
        rw [vertexEq] at member
        apply (coherent_iff problem degree a cell (.triple tripleIndex)).mpr
        exact valid.1 tripleIndex ((triple_mem problem tripleIndex).mp member) cell
    | element color atom =>
        rw [vertexEq] at member
        rcases (element_mem problem color atom).mp member with ⟨atomBound,degreeThree⟩
        simpa [vertexKind,PeriodicOneInThree.ClauseHolds,clauseValues_eq problem degree] using
          valid.2 color atom atomBound degreeThree cell

def indexedAssignment (problem : PeriodicThreeDM) (a : ContractedEdgeOrientation) :
    Nat → Cell → Bool := fun index =>
      a (problem.contractedEdges.getD index (.retained .red 0 ⟨0,(0,0)⟩))

theorem indexedAssignment_at (problem : PeriodicThreeDM) (a : ContractedEdgeOrientation)
    {edge : ContractedEdge} (member : edge ∈ problem.contractedEdges) (cell : Cell) :
    edgeAssignment problem (indexedAssignment problem a) edge cell = a edge cell := by
  simp [edgeAssignment,indexedAssignment,List.getD,List.getElem?_idxOf member]

private theorem endpoint_indexed (problem : PeriodicThreeDM) (a : ContractedEdgeOrientation)
    {endpoint : ContractedEndpoint} (member : endpoint ∈ problem.contractedEndpoints) (cell : Cell) :
    endpoint.edgeInward (edgeAssignment problem (indexedAssignment problem a)) cell =
      endpoint.edgeInward a cell := by
  have edgeMember := endpoint.edge_mem_of_mem member
  cases endpoint <;> simp only [ContractedEndpoint.edge] at edgeMember <;>
    simp only [ContractedEndpoint.edgeInward,indexedAssignment_at problem a edgeMember]

theorem hasOrientation_iff (problem : PeriodicThreeDM) (degree : problem.DegreeTwoOrThree) :
    TrichromaticGraphOrientation.HasOrientation (input problem) ↔ problem.HasContractedEdgeOrientation := by
  constructor
  · rintro ⟨a,valid⟩
    exact ⟨edgeAssignment problem a,(orientation_iff problem degree a).mp valid⟩
  · rintro ⟨a,valid⟩
    refine ⟨indexedAssignment problem a,(orientation_iff problem degree _).mpr ?_⟩
    constructor
    · intro index bound cell first firstMember second secondMember
      rw [endpoint_indexed problem a ((problem.contractedEndpointsAt_mem_iff _ _).mp firstMember).1,
        endpoint_indexed problem a ((problem.contractedEndpointsAt_mem_iff _ _).mp secondMember).1]
      exact valid.1 index bound cell first firstMember second secondMember
    · intro color atom bound degreeThree cell
      have same : (problem.contractedEndpointsAt (.element color atom)).map
          (fun endpoint => endpoint.edgeInward (edgeAssignment problem (indexedAssignment problem a)) cell) =
          (problem.contractedEndpointsAt (.element color atom)).map
            (fun endpoint => endpoint.edgeInward a cell) := by
        apply List.map_congr_left
        intro endpoint member
        exact endpoint_indexed problem a ((problem.contractedEndpointsAt_mem_iff _ _).mp member).1 cell
      rw [same]
      exact valid.2 color atom bound degreeThree cell

theorem problem_iff (problem : PeriodicThreeDM) (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree) :
    Problem (input problem) ↔ problem.Satisfiable := by
  rw [Problem,and_iff_right (input_wellFormed problem wellFormed degree),
    hasOrientation_iff problem degree,hasContractedEdgeOrientation_iff_satisfiable problem wellFormed degree]

open Lean Elab Command in
run_cmd do
  let name := ``problem_iff
  let axioms ← Lean.collectAxioms name
  let extra := axioms.filter fun ax =>
    ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
  unless extra.isEmpty do throwError "{name} depends on unexpected axioms: {extra}"

end LeanTrominoes.PeriodicThreeDM.GraphOrientationEncoding
