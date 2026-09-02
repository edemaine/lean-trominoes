/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripCountedContractedIncidenceEdgeBlockSemantics
import LeanTrominoes.PeriodicCNFStripHorizontalContractedDirectionBlockListData

/-! # Counted blocks as canonical horizontal contracted edges -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction
namespace CountedContractedIncidence

open Gadget PeriodicThreeDM

/-- Canonical color-major, element-major enumeration of colored elements. -/
def horizontalElementPairs (problem : PeriodicThreeDM) :
    List (WireColor × Nat) :=
  incidenceColors.flatMap fun color =>
    (List.range (problem.elementCount color)).map fun atom =>
      (color, atom)

/-- Actual incidence degree of every canonical colored element. -/
def horizontalElementDegrees (problem : PeriodicThreeDM) : List Nat :=
  (horizontalElementPairs problem).map fun pair =>
    problem.degree pair.1 pair.2

/-- Direction bodies of the incidences at one colored element, in the same
triple-index order used by executable contraction. -/
def horizontalIncidenceDirectionBodiesForElement
    (problem : PeriodicThreeDM)
    (incidenceBlock : IncidenceTag → HorizontalTypedIncidenceDirectionBlock)
    (pair : WireColor × Nat) : List (List AxisDirection) :=
  (problem.incidences pair.1 pair.2).map fun incidence =>
    (incidenceBlock ⟨incidence.tripleIndex, pair.1⟩).directions

/-- All incidence direction bodies reordered canonically by colored element. -/
def horizontalIncidenceDirectionBodiesByElement
    (problem : PeriodicThreeDM)
    (incidenceBlock : IncidenceTag → HorizontalTypedIncidenceDirectionBlock) :
    List (List AxisDirection) :=
  (horizontalElementPairs problem).flatMap
    (horizontalIncidenceDirectionBodiesForElement problem incidenceBlock)

private theorem edgeBlocks_elementPairs
    (problem : PeriodicThreeDM)
    (incidenceBlock : IncidenceTag → HorizontalTypedIncidenceDirectionBlock)
    (pairs : List (WireColor × Nat))
    (valid : ∀ pair ∈ pairs,
      problem.degree pair.1 pair.2 = 2 ∨
        problem.degree pair.1 pair.2 = 3) :
    edgeBlocks
        (pairs.map fun pair => problem.degree pair.1 pair.2)
        (pairs.flatMap
          (horizontalIncidenceDirectionBodiesForElement
            problem incidenceBlock)) =
      pairs.flatMap fun pair =>
        (horizontalContractedDirectionBlocksForElement
          problem incidenceBlock pair.1 pair.2).map fun tagged =>
            HorizontalContractedRoutedRequest.ContractedBlock.assemblerEdge
              tagged.2 := by
  induction pairs with
  | nil => rfl
  | cons pair pairs induction =>
      have headValid := valid pair (by simp)
      have tailValid : ∀ other ∈ pairs,
          problem.degree other.1 other.2 = 2 ∨
            problem.degree other.1 other.2 = 3 := by
        intro other member
        exact valid other (by simp [member])
      rcases headValid with degree | degree
      · have degreeEq : problem.degree pair.1 pair.2 = 2 := degree
        unfold PeriodicThreeDM.degree at degree
        generalize incidencesEq :
          problem.incidences pair.1 pair.2 = incidences at degree
        change incidences.length = 2 at degree
        rcases incidences with _ | ⟨first, incidences⟩
        · simp at degree
        rcases incidences with _ | ⟨second, incidences⟩
        · simp at degree
        rcases incidences with _ | ⟨third, incidences⟩
        · simp only [List.map_cons, List.flatMap_cons]
          rw [degreeEq]
          simp [
            horizontalIncidenceDirectionBodiesForElement,
            incidencesEq,
            horizontalContractedDirectionBlocksForElement,
            edgeBlocks,
            HorizontalContractedRoutedRequest.ContractedBlock.assemblerEdge]
          exact induction tailValid
        · simp at degree
      · have degreeEq : problem.degree pair.1 pair.2 = 3 := degree
        unfold PeriodicThreeDM.degree at degree
        generalize incidencesEq :
          problem.incidences pair.1 pair.2 = incidences at degree
        change incidences.length = 3 at degree
        rcases incidences with _ | ⟨first, incidences⟩
        · simp at degree
        rcases incidences with _ | ⟨second, incidences⟩
        · simp at degree
        rcases incidences with _ | ⟨third, incidences⟩
        · simp at degree
        rcases incidences with _ | ⟨fourth, incidences⟩
        · simp only [List.map_cons, List.flatMap_cons]
          rw [degreeEq]
          simp [
            horizontalIncidenceDirectionBodiesForElement,
            incidencesEq,
            horizontalContractedDirectionBlocksForElement,
            edgeBlocks,
            HorizontalContractedRoutedRequest.ContractedBlock.assemblerEdge]
          exact induction tailValid
        · simp at degree

/-- Under the degree promise, regrouping the actual element-major incidence
bodies gives exactly the assembler edge underlying every canonical compact
horizontal contracted block. -/
theorem edgeBlocks_horizontalIncidenceDirectionBodiesByElement
    (problem : PeriodicThreeDM)
    (incidenceBlock : IncidenceTag → HorizontalTypedIncidenceDirectionBlock)
    (degreeTwoOrThree : problem.DegreeTwoOrThree) :
    edgeBlocks
        (horizontalElementDegrees problem)
        (horizontalIncidenceDirectionBodiesByElement problem incidenceBlock) =
      (horizontalContractedDirectionBlocks problem incidenceBlock).map
        (fun tagged =>
          HorizontalContractedRoutedRequest.ContractedBlock.assemblerEdge
            tagged.2) := by
  have pairsValid : ∀ pair ∈ horizontalElementPairs problem,
      problem.degree pair.1 pair.2 = 2 ∨
        problem.degree pair.1 pair.2 = 3 := by
    intro pair member
    unfold horizontalElementPairs at member
    simp only [List.mem_flatMap, List.mem_map] at member
    obtain ⟨color, _colorMember, atom, atomMember, rfl⟩ := member
    have degree := degreeTwoOrThree color atom
      (List.mem_range.mp atomMember)
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using degree
  rw [show horizontalElementDegrees problem =
      (horizontalElementPairs problem).map fun pair =>
        problem.degree pair.1 pair.2 by rfl]
  rw [show horizontalIncidenceDirectionBodiesByElement
      problem incidenceBlock =
      (horizontalElementPairs problem).flatMap
        (horizontalIncidenceDirectionBodiesForElement
          problem incidenceBlock) by rfl]
  rw [edgeBlocks_elementPairs problem incidenceBlock
    (horizontalElementPairs problem) pairsValid]
  unfold horizontalElementPairs horizontalContractedDirectionBlocks
  rw [List.flatMap_assoc, List.map_flatMap]
  apply List.flatMap_congr
  intro color _colorMember
  rw [List.flatMap_map, List.map_flatMap]

end CountedContractedIncidence
end LeanTrominoes.PeriodicCNFStripReduction

end
