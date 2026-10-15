/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Tiling.Tromino.Strip.Counted.PeriodicCNFStripCountedContractedIncidenceSourceFilter
import LeanTrominoes.Computation.Encoding.Unary.UnaryFieldBooleanFilterNativeListCompiler

/-! # Target-field selection for retained and through contracted edges -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction.CountedContractedIncidence
open Computability Turing Gadget PeriodicThreeDM

/-- A through edge ends at its second incidence; retained edges use their sole incidence. -/
def keepTarget : ContractedDirectionAssembler.Role → Bool
  | .retained | .throughSecond => true
  | .throughFirst => false

def targetControls (sizes : List Nat) : List Bool :=
  (roles sizes).flatMap fun role => [keepTarget role]

def targetControlBlock (size : Nat) : List Bool :=
  if size = 3 then [true, true, true] else [false, true]

@[simp] theorem targetControls_cons_two (sizes : List Nat) :
    targetControls (2 :: sizes) = [false, true] ++ targetControls sizes := by
  unfold targetControls
  rw [roles_cons_two, List.flatMap_append]
  rfl

@[simp] theorem targetControls_cons_three (sizes : List Nat) :
    targetControls (3 :: sizes) = [true, true, true] ++ targetControls sizes := by
  unfold targetControls
  rw [roles_cons_three, List.flatMap_append]
  rfl

theorem targetControls_eq_blocks (sizes : List Nat)
    (valid : ∀ size ∈ sizes, size = 2 ∨ size = 3) :
    targetControls sizes = sizes.flatMap targetControlBlock := by
  induction sizes with
  | nil => rfl
  | cons size sizes ih =>
      have tailValid : ∀ other ∈ sizes, other = 2 ∨ other = 3 :=
        fun other member => valid other (by simp [member])
      rcases valid size (by simp) with rfl | rfl <;>
        simp [targetControlBlock, ih tailValid]

noncomputable def targetControlsComputableInPolyTime :
    TM2ComputableInPolyTime UnaryFieldEncoderMachine.unaryFields id targetControls := by
  unfold targetControls
  exact TM2CompositionMachine.computableInPolyTime rolesComputableInPolyTime
    (FiniteBlockTransducer.computableInPolyTime (fun role => [keepTarget role]))

private theorem targetControlBlock_length (size : Nat) (valid : size = 2 ∨ size = 3) :
    (targetControlBlock size).length = size := by
  rcases valid with rfl | rfl <;> rfl

private theorem selected_element_targets (problem : PeriodicThreeDM)
    (field : IncidenceTag → Nat) (color : WireColor) (atom : Nat)
    (valid : problem.degree color atom = 2 ∨ problem.degree color atom = 3) :
    UnaryFieldBooleanFilter.selectedValues (targetControlBlock (problem.degree color atom))
        ((problem.incidences color atom).map fun incidence => field ⟨incidence.tripleIndex, color⟩) =
      (problem.contractedEdgesForElement color atom).map (fun edge => field edge.targetTag) := by
  unfold PeriodicThreeDM.degree at valid ⊢
  unfold PeriodicThreeDM.contractedEdgesForElement
  generalize problem.incidences color atom = incidences at valid ⊢
  revert valid
  cases incidences with
  | nil => simp
  | cons first rest =>
      cases rest with
      | nil => simp
      | cons second rest =>
          cases rest with
          | nil =>
              intro _
              simp [targetControlBlock, UnaryFieldBooleanFilter.selectedValues_eq,
                DelimitedBinaryWordBooleanFilter.selected, ContractedEdge.targetTag]
          | cons third rest =>
              cases rest with
              | nil =>
                  intro _
                  simp [targetControlBlock, UnaryFieldBooleanFilter.selectedValues_eq,
                    DelimitedBinaryWordBooleanFilter.selected, ContractedEdge.targetTag]
              | cons fourth rest => simp

/-- Select target incidence fields in exactly the canonical contracted-edge order. -/
theorem selected_targets_eq_contracted (problem : PeriodicThreeDM)
    (field : IncidenceTag → Nat) (degreeTwoOrThree : problem.DegreeTwoOrThree) :
    UnaryFieldBooleanFilter.selectedValues
        (targetControls (horizontalElementDegrees problem))
        ((horizontalElementPairs problem).flatMap fun element =>
          (problem.incidences element.1 element.2).map fun incidence => field ⟨incidence.tripleIndex, element.1⟩) =
      problem.contractedEdges.map (fun edge => field edge.targetTag) := by
  have valid : ∀ element ∈ horizontalElementPairs problem,
      problem.degree element.1 element.2 = 2 ∨ problem.degree element.1 element.2 = 3 := by
    intro element member
    simp only [horizontalElementPairs, List.mem_flatMap, List.mem_map] at member
    obtain ⟨color, _, atom, atomMember, rfl⟩ := member
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using
      degreeTwoOrThree color atom (List.mem_range.mp atomMember)
  unfold horizontalElementDegrees
  rw [targetControls_eq_blocks _ (by
    intro size member
    obtain ⟨element, elementMember, rfl⟩ := List.mem_map.mp member
    exact valid element elementMember), List.flatMap_map,
    UnaryFieldBooleanFilter.selectedValues_flatMap _ _ _ (by
      intro element member
      rw [List.length_map, targetControlBlock_length _ (valid element member)]
      rfl)]
  have selected := List.flatMap_congr (fun element member =>
    selected_element_targets problem field element.1 element.2 (valid element member))
  refine selected.trans ?_
  simp only [horizontalElementPairs, PeriodicThreeDM.contractedEdges,
    PeriodicThreeDM.contractedEdgesForColor, List.flatMap_assoc, List.flatMap_map, List.map_flatMap]

end LeanTrominoes.PeriodicCNFStripReduction.CountedContractedIncidence
end
