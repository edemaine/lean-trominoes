import LeanTrominoes.PeriodicThreeDMContractionSemantics

/-!
# Contracted colored graph of a periodic 3DM instance

This file makes the graph operation behind Theorem 3.8 executable.  A
degree-three colored element is retained, contributing its three original
triple-to-element edges.  A degree-two colored element is suppressed,
contributing one edge between its two incident triple vertices.  Its offset
is the difference of the two original incidence offsets, so the construction
is correct in every translate of the periodic lift.

The edge object retains the original incidence metadata at both ends.  This
will let the geometric normalization concatenate the corresponding routes
and transport endpoint orientations without reconstructing incidences from
coordinates.
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- One colored edge after suppressing degree-two colored elements.

* `retained` is an original triple-to-degree-three-element incidence;
* `through` concatenates the two incidences of a suppressed element.
-/
inductive ContractedEdge
  | retained
      (color : WireColor) (atom : Nat)
      (incidence : Incidence)
  | through
      (color : WireColor) (atom : Nat)
      (first second : Incidence)
  deriving DecidableEq, Repr

namespace ContractedEdge

/-- Color inherited from the colored 3DM element. -/
def color : ContractedEdge → WireColor
  | .retained color _ _ | .through color _ _ _ => color

/-- Colored element responsible for this retained or contracted edge. -/
def atom : ContractedEdge → Nat
  | .retained _ atom _ | .through _ atom _ _ => atom

/-- Original incidence tag at the source triple endpoint. -/
def sourceTag : ContractedEdge → IncidenceTag
  | .retained color _ incidence
  | .through color _ incidence _ =>
      ⟨incidence.tripleIndex, color⟩

/-- Original incidence tag represented at the target endpoint.  A retained
edge uses the same incidence at its colored-element endpoint; a through edge
uses the second incidence at its second triple endpoint. -/
def targetTag : ContractedEdge → IncidenceTag
  | .retained color _ incidence =>
      ⟨incidence.tripleIndex, color⟩
  | .through color _ _ incidence =>
      ⟨incidence.tripleIndex, color⟩

/-- Original incidence based at the source triple. -/
def sourceIncidence : ContractedEdge → Incidence
  | .retained _ _ incidence
  | .through _ _ incidence _ => incidence

/-- Original incidence represented at the target.  On a retained edge this
is the same incidence, while on a through edge it is the second incidence of
the suppressed element. -/
def targetIncidence : ContractedEdge → Incidence
  | .retained _ _ incidence => incidence
  | .through _ _ _ incidence => incidence

/-- Whether the target endpoint is a retained monochromatic vertex rather
than another trichromatic triple vertex. -/
def targetIsElement : ContractedEdge → Bool
  | .retained _ _ _ => true
  | .through _ _ _ _ => false

/-- Forget the color and incidence metadata, producing the ordinary
periodic protoedge.  If the two incidences of a suppressed element have
offsets `d₁` and `d₂`, then the second triple lies at translate `d₁ - d₂`
relative to the first. -/
def toPeriodicEdge :
    ContractedEdge → PeriodicEdge PeriodicThreeDMVertex
  | .retained color atom incidence =>
      ⟨.triple incidence.tripleIndex, .element color atom,
        incidence.offset⟩
  | .through _color _atom first second =>
      ⟨.triple first.tripleIndex, .triple second.tripleIndex,
        Cell.sub first.offset second.offset⟩

@[simp]
theorem color_retained (color : WireColor) (atom : Nat)
    (incidence : Incidence) :
    (ContractedEdge.retained color atom incidence).color = color := by
  rfl

@[simp]
theorem color_through (color : WireColor) (atom : Nat)
    (first second : Incidence) :
    (ContractedEdge.through color atom first second).color = color := by
  rfl

@[simp]
theorem toPeriodicEdge_retained (color : WireColor) (atom : Nat)
    (incidence : Incidence) :
    (ContractedEdge.retained color atom incidence).toPeriodicEdge =
      ⟨.triple incidence.tripleIndex, .element color atom,
        incidence.offset⟩ := by
  rfl

@[simp]
theorem toPeriodicEdge_through (color : WireColor) (atom : Nat)
    (first second : Incidence) :
    (ContractedEdge.through color atom first second).toPeriodicEdge =
      ⟨.triple first.tripleIndex, .triple second.tripleIndex,
        Cell.sub first.offset second.offset⟩ := by
  rfl

/-- The contracted edge remembers the original incidence tags represented
at its endpoint or endpoints. -/
def incidenceTags : ContractedEdge → List IncidenceTag
  | edge@(.retained ..) => [edge.sourceTag]
  | edge@(.through ..) => [edge.sourceTag, edge.targetTag]

end ContractedEdge

/-- Edges contributed by one colored element.  Unexpected degrees produce
no edges; under `DegreeTwoOrThree` only the two displayed cases occur. -/
def contractedEdgesForElement (problem : PeriodicThreeDM)
    (color : WireColor) (atom : Nat) : List ContractedEdge :=
  match problem.incidences color atom with
  | [first, second] =>
      [.through color atom first second]
  | [first, second, third] =>
      [.retained color atom first,
        .retained color atom second,
        .retained color atom third]
  | _ => []

/-- All contracted edges of one color, grouped by colored element. -/
def contractedEdgesForColor (problem : PeriodicThreeDM)
    (color : WireColor) : List ContractedEdge :=
  (List.range (problem.elementCount color)).flatMap
    (problem.contractedEdgesForElement color)

/-- Complete colored edge list after suppressing every degree-two element. -/
def contractedEdges (problem : PeriodicThreeDM) : List ContractedEdge :=
  incidenceColors.flatMap problem.contractedEdgesForColor

/-- Retained degree-three colored vertices of one color. -/
def contractedElementVerticesForColor (problem : PeriodicThreeDM)
    (color : WireColor) : List PeriodicThreeDMVertex :=
  ((List.range (problem.elementCount color)).filter fun atom =>
      problem.degree color atom = 3).map
    (PeriodicThreeDMVertex.element color)

/-- All retained monochromatic vertices.  Degree-two colored vertices do not
appear because their two incidences have become one through edge. -/
def contractedElementVertices (problem : PeriodicThreeDM) :
    List PeriodicThreeDMVertex :=
  incidenceColors.flatMap problem.contractedElementVerticesForColor

/-- The executable periodic graph obtained by degree-two suppression. -/
def contractedGraph (problem : PeriodicThreeDM) :
    PeriodicGraph PeriodicThreeDMVertex where
  vertices := problem.tripleVertices ++
    problem.contractedElementVertices
  edges := problem.contractedEdges.map ContractedEdge.toPeriodicEdge

@[simp]
theorem contractedEdgesForElement_of_incidences_pair
    (problem : PeriodicThreeDM) (color : WireColor) (atom : Nat)
    (first second : Incidence)
    (incidences :
      problem.incidences color atom = [first, second]) :
    problem.contractedEdgesForElement color atom =
      [.through color atom first second] := by
  simp [contractedEdgesForElement, incidences]

@[simp]
theorem contractedEdgesForElement_of_incidences_triple
    (problem : PeriodicThreeDM) (color : WireColor) (atom : Nat)
    (first second third : Incidence)
    (incidences :
      problem.incidences color atom = [first, second, third]) :
    problem.contractedEdgesForElement color atom =
      [.retained color atom first,
        .retained color atom second,
        .retained color atom third] := by
  simp [contractedEdgesForElement, incidences]

/-- A degree-two colored element contributes exactly one contracted edge. -/
theorem contractedEdgesForElement_length_of_degree_two
    (problem : PeriodicThreeDM) (color : WireColor) (atom : Nat)
    (degree : problem.degree color atom = 2) :
    (problem.contractedEdgesForElement color atom).length = 1 := by
  unfold PeriodicThreeDM.degree at degree
  unfold contractedEdgesForElement
  generalize incidencesEq :
      problem.incidences color atom = incidences at degree
  change incidences.length = 2 at degree
  rcases incidences with _ | ⟨first, incidences⟩
  · simp at degree
  rcases incidences with _ | ⟨second, incidences⟩
  · simp at degree
  rcases incidences with _ | ⟨third, incidences⟩
  · rfl
  simp at degree

/-- A degree-three colored element contributes its three retained edges. -/
theorem contractedEdgesForElement_length_of_degree_three
    (problem : PeriodicThreeDM) (color : WireColor) (atom : Nat)
    (degree : problem.degree color atom = 3) :
    (problem.contractedEdgesForElement color atom).length = 3 := by
  unfold PeriodicThreeDM.degree at degree
  unfold contractedEdgesForElement
  generalize incidencesEq :
      problem.incidences color atom = incidences at degree
  change incidences.length = 3 at degree
  rcases incidences with _ | ⟨first, incidences⟩
  · simp at degree
  rcases incidences with _ | ⟨second, incidences⟩
  · simp at degree
  rcases incidences with _ | ⟨third, incidences⟩
  · simp at degree
  rcases incidences with _ | ⟨fourth, incidences⟩
  · rfl
  simp at degree

/-- Every edge emitted for one element inherits that element's color and
atom. -/
theorem contractedEdgesForElement_metadata
    (problem : PeriodicThreeDM) (color : WireColor) (atom : Nat)
    {edge : ContractedEdge}
    (member : edge ∈ problem.contractedEdgesForElement color atom) :
    edge.color = color ∧ edge.atom = atom := by
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
    exact ⟨rfl, rfl⟩
  rcases incidences with _ | ⟨fourth, incidences⟩
  · simp at member
    rcases member with rfl | rfl | rfl <;>
      exact ⟨rfl, rfl⟩
  simp at member

/-- Both incidence records stored by an emitted edge really belong to the
colored element that generated it.  The final disjunction records whether
the element was suppressed or retained. -/
theorem contractedEdgesForElement_incidence_members
    (problem : PeriodicThreeDM) (color : WireColor) (atom : Nat)
    {edge : ContractedEdge}
    (member : edge ∈ problem.contractedEdgesForElement color atom) :
    edge.sourceIncidence ∈ problem.incidences color atom ∧
      edge.targetIncidence ∈ problem.incidences color atom ∧
      (problem.degree color atom = 2 ∧
          edge.targetIsElement = false ∨
        problem.degree color atom = 3 ∧
          edge.targetIsElement = true) := by
  unfold contractedEdgesForElement at member
  generalize incidencesEq :
      problem.incidences color atom = incidences at member ⊢
  rcases incidences with _ | ⟨first, incidences⟩
  · simp at member
  rcases incidences with _ | ⟨second, incidences⟩
  · simp at member
  rcases incidences with _ | ⟨third, incidences⟩
  · simp only [List.mem_singleton] at member
    subst edge
    constructor
    · simp [ContractedEdge.sourceIncidence]
    constructor
    · simp [ContractedEdge.targetIncidence]
    left
    constructor
    · rw [PeriodicThreeDM.degree, incidencesEq]
      rfl
    · rfl
  rcases incidences with _ | ⟨fourth, incidences⟩
  · simp at member
    rcases member with rfl | rfl | rfl
    all_goals
      constructor
      · simp [ContractedEdge.sourceIncidence]
      constructor
      · simp [ContractedEdge.targetIncidence]
      right
      constructor
      · rw [PeriodicThreeDM.degree, incidencesEq]
        rfl
      · rfl
  simp at member

/-- Every emitted contracted edge has one of the three 3DM colors. -/
theorem contractedEdge_color_mem
    (problem : PeriodicThreeDM) {edge : ContractedEdge}
    (member : edge ∈ problem.contractedEdges) :
    edge.color ∈ incidenceColors := by
  simp only [contractedEdges, List.mem_flatMap] at member
  rcases member with ⟨color, colorMember, edgeMember⟩
  simp only [contractedEdgesForColor, List.mem_flatMap] at edgeMember
  rcases edgeMember with ⟨atom, atomMember, edgeMember⟩
  exact (contractedEdgesForElement_metadata
    problem color atom edgeMember).1 ▸ colorMember

theorem contractedElementVerticesForColor_nodup
    (problem : PeriodicThreeDM) (color : WireColor) :
    (problem.contractedElementVerticesForColor color).Nodup := by
  apply (List.nodup_range.filter _).map
  intro first second equality
  cases equality
  rfl

@[simp]
theorem contractedElementVerticesForColor_mem_iff
    (problem : PeriodicThreeDM) (color : WireColor) (atom : Nat) :
    .element color atom ∈
        problem.contractedElementVerticesForColor color ↔
      atom < problem.elementCount color ∧
        problem.degree color atom = 3 := by
  simp [contractedElementVerticesForColor]

theorem contractedElementVerticesForColor_disjoint
    (problem : PeriodicThreeDM)
    {first second : WireColor} (different : first ≠ second) :
    List.Disjoint
      (problem.contractedElementVerticesForColor first)
      (problem.contractedElementVerticesForColor second) := by
  rw [List.disjoint_left]
  intro vertex firstMem secondMem
  simp only [contractedElementVerticesForColor,
    List.mem_map] at firstMem secondMem
  rcases firstMem with ⟨firstAtom, _, rfl⟩
  rcases secondMem with ⟨secondAtom, _, equality⟩
  cases equality
  exact different rfl

theorem contractedElementVertices_nodup
    (problem : PeriodicThreeDM) :
    problem.contractedElementVertices.Nodup := by
  simp only [contractedElementVertices, incidenceColors,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [List.nodup_append]
  refine
    ⟨contractedElementVerticesForColor_nodup problem .red, ?_, ?_⟩
  · rw [List.nodup_append]
    exact
      ⟨contractedElementVerticesForColor_nodup problem .green,
        contractedElementVerticesForColor_nodup problem .blue,
        by
          intro greenVertex greenMem blueVertex blueMem equal
          subst blueVertex
          exact
            (List.disjoint_left.mp
              (contractedElementVerticesForColor_disjoint problem
                (first := .green) (second := .blue) (by decide))
              greenMem) blueMem⟩
  ·
    intro redVertex redMem otherVertex otherMem
    rw [List.mem_append] at otherMem
    rcases otherMem with greenMem | blueMem
    · intro equal
      subst otherVertex
      exact
        (List.disjoint_left.mp
          (contractedElementVerticesForColor_disjoint problem
            (first := .red) (second := .green) (by decide))
          redMem) greenMem
    · intro equal
      subst otherVertex
      exact
        (List.disjoint_left.mp
          (contractedElementVerticesForColor_disjoint problem
            (first := .red) (second := .blue) (by decide))
          redMem) blueMem

theorem triple_contractedElementVertices_disjoint
    (problem : PeriodicThreeDM) :
    ∀ triple ∈ problem.tripleVertices,
      ∀ element ∈ problem.contractedElementVertices,
        triple ≠ element := by
  intro triple tripleMem element elementMem equal
  simp only [tripleVertices, List.mem_map] at tripleMem
  rcases tripleMem with ⟨tripleIndex, _, rfl⟩
  cases element with
  | triple elementIndex =>
      simp [contractedElementVertices,
        contractedElementVerticesForColor] at elementMem
  | element color atom =>
      cases equal

/-- Suppression produces a duplicate-free prototype-vertex list. -/
theorem contractedGraph_vertices_nodup
    (problem : PeriodicThreeDM) :
    problem.contractedGraph.vertices.Nodup := by
  change
    (problem.tripleVertices ++
      problem.contractedElementVertices).Nodup
  rw [List.nodup_append]
  exact ⟨tripleVertices_nodup problem,
    contractedElementVertices_nodup problem,
    triple_contractedElementVertices_disjoint problem⟩

/-- The executable contracted graph lists both endpoints of every emitted
edge. -/
theorem contractedGraph_isWellFormed
    (problem : PeriodicThreeDM) :
    problem.contractedGraph.IsWellFormed := by
  constructor
  · exact contractedGraph_vertices_nodup problem
  · intro graphEdge graphEdgeMem
    simp only [contractedGraph, List.mem_map] at graphEdgeMem
    rcases graphEdgeMem with ⟨edge, edgeMem, rfl⟩
    simp only [contractedEdges, List.mem_flatMap] at edgeMem
    rcases edgeMem with ⟨color, colorMem, edgeMem⟩
    simp only [contractedEdgesForColor,
      List.mem_flatMap] at edgeMem
    rcases edgeMem with ⟨atom, atomMem, edgeMem⟩
    have atomLt : atom < problem.elementCount color :=
      List.mem_range.mp atomMem
    have incidenceMembers :=
      contractedEdgesForElement_incidence_members
        problem color atom edgeMem
    have sourceLt :=
      incidence_tripleIndex_lt problem color atom
        incidenceMembers.1
    have targetLt :=
      incidence_tripleIndex_lt problem color atom
        incidenceMembers.2.1
    constructor
    · apply List.mem_append_left
      exact List.mem_map.mpr
        ⟨edge.sourceIncidence.tripleIndex,
          List.mem_range.mpr sourceLt, by
            cases edge <;> rfl⟩
    · cases edge with
      | retained edgeColor edgeAtom incidence =>
          apply List.mem_append_right
          apply List.mem_flatMap.mpr
          have metadata :=
            contractedEdgesForElement_metadata
              problem color atom edgeMem
          simp only [ContractedEdge.color,
            ContractedEdge.atom] at metadata
          rcases metadata with ⟨rfl, rfl⟩
          refine ⟨edgeColor, colorMem, ?_⟩
          · simp only [ContractedEdge.toPeriodicEdge]
            apply
              (contractedElementVerticesForColor_mem_iff
                problem edgeColor edgeAtom).2
            refine ⟨atomLt, ?_⟩
            rcases incidenceMembers.2.2 with
              impossible | retained
            · simp [ContractedEdge.targetIsElement] at impossible
            · exact retained.1
      | through edgeColor edgeAtom first second =>
          apply List.mem_append_left
          exact List.mem_map.mpr
            ⟨second.tripleIndex,
              List.mem_range.mpr targetLt, rfl⟩

end PeriodicThreeDM

end LeanTrominoes
