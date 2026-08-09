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
        simp only [incidenceColors, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, Nat.add_zero]
        rw [show
          ((List.range problem.redCount).map fun blockAtom =>
            if WireColor.red = WireColor.red ∧ blockAtom = atom ∧
                problem.degree .red blockAtom = 3 then 3 else 0).sum = 3 by
              have pointwise :
                  (List.range problem.redCount).map (fun blockAtom =>
                    if WireColor.red = WireColor.red ∧ blockAtom = atom ∧
                        problem.degree .red blockAtom = 3 then 3 else 0) =
                    (List.range problem.redCount).map (fun blockAtom =>
                      if blockAtom = atom then 3 else 0) := by
                apply List.map_congr_left
                intro blockAtom blockAtomMember
                by_cases equal : blockAtom = atom
                · subst blockAtom
                  simp [degree]
                · simp [equal]
              rw [pointwise]
              exact sum_range_indicator problem.redCount atom 3 atomLt]
        simp
      | green =>
        simp only [incidenceColors, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, Nat.add_zero]
        rw [show
          ((List.range problem.greenCount).map fun blockAtom =>
            if WireColor.green = WireColor.green ∧ blockAtom = atom ∧
                problem.degree .green blockAtom = 3 then 3 else 0).sum = 3 by
              have pointwise :
                  (List.range problem.greenCount).map (fun blockAtom =>
                    if WireColor.green = WireColor.green ∧ blockAtom = atom ∧
                        problem.degree .green blockAtom = 3 then 3 else 0) =
                    (List.range problem.greenCount).map (fun blockAtom =>
                      if blockAtom = atom then 3 else 0) := by
                apply List.map_congr_left
                intro blockAtom blockAtomMember
                by_cases equal : blockAtom = atom
                · subst blockAtom
                  simp [degree]
                · simp [equal]
              rw [pointwise]
              exact sum_range_indicator problem.greenCount atom 3 atomLt]
        simp
      | blue =>
        simp only [incidenceColors, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, Nat.add_zero]
        rw [show
          ((List.range problem.blueCount).map fun blockAtom =>
            if WireColor.blue = WireColor.blue ∧ blockAtom = atom ∧
                problem.degree .blue blockAtom = 3 then 3 else 0).sum = 3 by
              have pointwise :
                  (List.range problem.blueCount).map (fun blockAtom =>
                    if WireColor.blue = WireColor.blue ∧ blockAtom = atom ∧
                        problem.degree .blue blockAtom = 3 then 3 else 0) =
                    (List.range problem.blueCount).map (fun blockAtom =>
                      if blockAtom = atom then 3 else 0) := by
                apply List.map_congr_left
                intro blockAtom blockAtomMember
                by_cases equal : blockAtom = atom
                · subst blockAtom
                  simp [degree]
                · simp [equal]
              rw [pointwise]
              exact sum_range_indicator problem.blueCount atom 3 atomLt]
        simp

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

end PeriodicThreeDM
end LeanTrominoes
