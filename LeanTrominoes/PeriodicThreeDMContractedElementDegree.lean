import LeanTrominoes.PeriodicThreeDMContractedEndpointDegree

/-!
# Degree of retained monochromatic contracted vertices

A colored 3DM element is retained precisely when its original degree is
three.  Its local contracted-edge block then consists of three retained
edges, while every other color/atom block contributes zero incidences to
that prototype vertex.  This proves the monochromatic half of the exact
degree-three invariant needed by vertex normalization.
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- Counting across a flattened list is the sum of the counts in its
blocks. -/
theorem count_flatMap_eq_sum_count
    {α β : Type*} [BEq β] [LawfulBEq β]
    (items : List α) (blocks : α → List β) (value : β) :
    (items.flatMap blocks).count value =
      (items.map fun item => (blocks item).count value).sum := by
  induction items with
  | nil => rfl
  | cons item rest induction =>
      simp [induction, List.count_append]

/-- A single colored-element block contributes three incidences to its own
vertex exactly in the degree-three case, and none to a differently named
colored-element vertex. -/
theorem contractedEdgesForElement_element_count
    (problem : PeriodicThreeDM)
    (blockColor wantedColor : WireColor)
    (blockAtom wantedAtom : Nat) :
    ((problem.contractedEdgesForElement blockColor blockAtom).flatMap
      fun edge => edge.toPeriodicEdge.incidences).count
        (.element wantedColor wantedAtom) =
      if blockColor = wantedColor ∧ blockAtom = wantedAtom ∧
          problem.degree blockColor blockAtom = 3 then
        3
      else
        0 := by
  unfold contractedEdgesForElement PeriodicThreeDM.degree
  generalize incidencesEq :
      problem.incidences blockColor blockAtom = incidences
  rcases incidences with _ | ⟨first, incidences⟩
  · simp
  rcases incidences with _ | ⟨second, incidences⟩
  · simp
  rcases incidences with _ | ⟨third, incidences⟩
  · simp [ContractedEdge.toPeriodicEdge, PeriodicEdge.incidences]
  rcases incidences with _ | ⟨fourth, incidences⟩
  · by_cases colorEqual : blockColor = wantedColor
    · subst wantedColor
      by_cases atomEqual : blockAtom = wantedAtom
      · subst wantedAtom
        simp [ContractedEdge.toPeriodicEdge, PeriodicEdge.incidences]
      · simp [ContractedEdge.toPeriodicEdge, PeriodicEdge.incidences,
          atomEqual]
    · simp [ContractedEdge.toPeriodicEdge, PeriodicEdge.incidences,
        colorEqual]
  · simp

/-- In a numeric range, one selected in-range index contributes its given
weight exactly once. -/
theorem sum_range_indicator
    (bound wanted weight : Nat) (wantedLt : wanted < bound) :
    ((List.range bound).map fun index =>
      if index = wanted then weight else 0).sum = weight := by
  induction bound with
  | zero => simp at wantedLt
  | succ bound induction =>
      rw [List.range_succ, List.map_append, List.sum_append]
      by_cases below : wanted < bound
      · rw [induction below]
        have different : bound ≠ wanted := by omega
        simp [different]
      · have equal : bound = wanted := by omega
        subst wanted
        have allZero :
            (List.range bound).map (fun index =>
              if index = bound then weight else 0) =
              (List.range bound).map (fun _ => 0) := by
          apply List.map_congr_left
          intro index indexMember
          have indexLt : index < bound := List.mem_range.mp indexMember
          simp [Nat.ne_of_lt indexLt]
        rw [allZero]
        simp

/-- The unique selected index can additionally carry a decidable local
predicate known to hold there. -/
theorem sum_range_indicator_and
    (bound wanted weight : Nat) (predicate : Nat → Prop)
    [DecidablePred predicate]
    (wantedLt : wanted < bound) (wantedHolds : predicate wanted) :
    ((List.range bound).map fun index =>
      if index = wanted ∧ predicate index then weight else 0).sum = weight := by
  have pointwise :
      (List.range bound).map (fun index =>
        if index = wanted ∧ predicate index then weight else 0) =
      (List.range bound).map (fun index =>
        if index = wanted then weight else 0) := by
    apply List.map_congr_left
    intro index indexMember
    by_cases equal : index = wanted
    · subst index
      simp [wantedHolds]
    · simp [equal]
  rw [pointwise]
  exact sum_range_indicator bound wanted weight wantedLt

/-- The complete contracted graph has degree three at every retained
monochromatic element vertex. -/
theorem contractedGraph_element_degree_eq_three
    (problem : PeriodicThreeDM)
    (color : WireColor) (atom : Nat)
    (atomLt : atom < problem.elementCount color)
    (degree : problem.degree color atom = 3) :
    problem.contractedGraph.incidences.count (.element color atom) = 3 := by
  unfold contractedGraph PeriodicGraph.incidences contractedEdges
  rw [List.flatMap_map, List.flatMap_assoc,
    count_flatMap_eq_sum_count]
  simp only [contractedEdgesForColor, List.flatMap_assoc]
  change
    (incidenceColors.map (fun blockColor =>
      ((List.range (problem.elementCount blockColor)).flatMap
        (fun blockAtom =>
          (problem.contractedEdgesForElement blockColor blockAtom).flatMap
            fun edge => edge.toPeriodicEdge.incidences)).count
              (.element color atom))).sum = 3
  calc
    _ = (incidenceColors.map (fun blockColor =>
          ((List.range (problem.elementCount blockColor)).map
            (fun blockAtom =>
              if blockColor = color ∧ blockAtom = atom ∧
                  problem.degree blockColor blockAtom = 3 then
                3
              else
                0)).sum)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro blockColor blockColorMember
      rw [count_flatMap_eq_sum_count]
      apply congrArg List.sum
      apply List.map_congr_left
      intro blockAtom blockAtomMember
      exact contractedEdgesForElement_element_count
        problem blockColor color blockAtom atom
    _ = 3 := by
      cases color with
      | red =>
          simpa [incidenceColors, PeriodicThreeDM.elementCount] using
            sum_range_indicator_and problem.redCount atom 3
              (fun blockAtom => problem.degree .red blockAtom = 3)
              atomLt degree
      | green =>
          simpa [incidenceColors, PeriodicThreeDM.elementCount] using
            sum_range_indicator_and problem.greenCount atom 3
              (fun blockAtom => problem.degree .green blockAtom = 3)
              atomLt degree
      | blue =>
          simpa [incidenceColors, PeriodicThreeDM.elementCount] using
            sum_range_indicator_and problem.blueCount atom 3
              (fun blockAtom => problem.degree .blue blockAtom = 3)
              atomLt degree

/-- Every retained monochromatic vertex has exactly three executable
endpoint occurrences. -/
theorem contractedEndpointsAt_element_length
    (problem : PeriodicThreeDM)
    (color : WireColor) (atom : Nat)
    (atomLt : atom < problem.elementCount color)
    (degree : problem.degree color atom = 3) :
    (problem.contractedEndpointsAt (.element color atom)).length = 3 := by
  rw [contractedEndpointsAt_length_eq_degree]
  exact contractedGraph_element_degree_eq_three
    problem color atom atomLt degree

/-- Every retained contracted vertex is incident to a contracted edge.  The
triple and retained-element degree calculations above both give the stronger
fact that each such vertex has exactly three endpoint occurrences. -/
theorem contractedGraph_everyVertexIncident
    (problem : PeriodicThreeDM)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree) :
    PeriodicGridDrawing.EveryVertexIncident problem.contractedGraph := by
  apply PeriodicGridDrawing.everyVertexIncident_of_mem_incidences
  intro vertex vertexMember
  simp only [contractedGraph, List.mem_append] at vertexMember
  rcases vertexMember with tripleMember | elementMember
  · simp only [tripleVertices, List.mem_map] at tripleMember
    rcases tripleMember with ⟨tripleIndex, indexMember, rfl⟩
    have indexLt : tripleIndex < problem.triples.length := by
      simpa using indexMember
    apply List.count_pos_iff.mp
    rw [contractedGraph_triple_degree_eq_three
      problem wellFormed degree tripleIndex indexLt]
    omega
  · simp only [contractedElementVertices, List.mem_flatMap]
      at elementMember
    rcases elementMember with
      ⟨color, colorMember, elementMember⟩
    simp only [contractedElementVerticesForColor, List.mem_map]
      at elementMember
    rcases elementMember with ⟨atom, atomMember, rfl⟩
    have filtered := List.mem_filter.mp atomMember
    have atomLt : atom < problem.elementCount color := by
      simpa using filtered.1
    apply List.count_pos_iff.mp
    rw [contractedGraph_element_degree_eq_three
      problem color atom atomLt (of_decide_eq_true filtered.2)]
    omega

end PeriodicThreeDM
end LeanTrominoes
