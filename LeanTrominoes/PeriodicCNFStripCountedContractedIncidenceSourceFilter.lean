/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripCountedContractedIncidenceHorizontalEdgeBlockSemantics
import LeanTrominoes.UnaryFieldBooleanFilterNativeListCompiler

/-! # Source-field selection for retained and through contracted edges -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction.CountedContractedIncidence
open Computability Turing Gadget PeriodicThreeDM

/-- A through edge starts at its first incidence; every retained incidence starts an edge. -/
def keepSource : ContractedDirectionAssembler.Role → Bool
  | .retained | .throughFirst => true
  | .throughSecond => false

def sourceControls (sizes : List Nat) : List Bool :=
  (roles sizes).flatMap fun role => [keepSource role]

def sourceControlBlock (size : Nat) : List Bool :=
  if size = 3 then [true, true, true] else [true, false]

@[simp] theorem sourceControls_cons_two (sizes : List Nat) :
    sourceControls (2 :: sizes) = [true, false] ++ sourceControls sizes := by
  unfold sourceControls
  rw [roles_cons_two, List.flatMap_append]
  rfl

@[simp] theorem sourceControls_cons_three (sizes : List Nat) :
    sourceControls (3 :: sizes) = [true, true, true] ++ sourceControls sizes := by
  unfold sourceControls
  rw [roles_cons_three, List.flatMap_append]
  rfl

theorem sourceControls_eq_blocks (sizes : List Nat)
    (valid : ∀ size ∈ sizes, size = 2 ∨ size = 3) :
    sourceControls sizes = sizes.flatMap sourceControlBlock := by
  induction sizes with
  | nil => rfl
  | cons size sizes ih =>
      have tailValid : ∀ other ∈ sizes, other = 2 ∨ other = 3 :=
        fun other member => valid other (by simp [member])
      rcases valid size (by simp) with rfl | rfl <;>
        simp [sourceControlBlock, ih tailValid]

noncomputable def sourceControlsComputableInPolyTime :
    TM2ComputableInPolyTime UnaryFieldEncoderMachine.unaryFields id sourceControls := by
  unfold sourceControls
  exact TM2CompositionMachine.computableInPolyTime rolesComputableInPolyTime
    (FiniteBlockTransducer.computableInPolyTime (fun role => [keepSource role]))

private theorem sourceControlBlock_length (size : Nat) (valid : size = 2 ∨ size = 3) :
    (sourceControlBlock size).length = size := by
  rcases valid with rfl | rfl <;> rfl

private theorem selected_element_sources (problem : PeriodicThreeDM)
    (field : IncidenceTag → Nat) (color : WireColor) (atom : Nat)
    (valid : problem.degree color atom = 2 ∨ problem.degree color atom = 3) :
    UnaryFieldBooleanFilter.selectedValues (sourceControlBlock (problem.degree color atom))
        ((problem.incidences color atom).map fun incidence => field ⟨incidence.tripleIndex, color⟩) =
      (problem.contractedEdgesForElement color atom).map (fun edge => field edge.sourceTag) := by
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
              simp [sourceControlBlock, UnaryFieldBooleanFilter.selectedValues_eq,
                DelimitedBinaryWordBooleanFilter.selected, ContractedEdge.sourceTag]
          | cons third rest =>
              cases rest with
              | nil =>
                  intro _
                  simp [sourceControlBlock, UnaryFieldBooleanFilter.selectedValues_eq,
                    DelimitedBinaryWordBooleanFilter.selected, ContractedEdge.sourceTag]
              | cons fourth rest => simp

/-- Select source fields in exactly the canonical contracted-edge order. -/
theorem selected_sources_eq_contracted (problem : PeriodicThreeDM)
    (field : IncidenceTag → Nat) (degreeTwoOrThree : problem.DegreeTwoOrThree) :
    UnaryFieldBooleanFilter.selectedValues
        (sourceControls (horizontalElementDegrees problem))
        ((horizontalElementPairs problem).flatMap fun element =>
          (problem.incidences element.1 element.2).map fun incidence => field ⟨incidence.tripleIndex, element.1⟩) =
      problem.contractedEdges.map (fun edge => field edge.sourceTag) := by
  have valid : ∀ element ∈ horizontalElementPairs problem,
      problem.degree element.1 element.2 = 2 ∨ problem.degree element.1 element.2 = 3 := by
    intro element member
    simp only [horizontalElementPairs, List.mem_flatMap, List.mem_map] at member
    obtain ⟨color, _, atom, atomMember, rfl⟩ := member
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using
      degreeTwoOrThree color atom (List.mem_range.mp atomMember)
  unfold horizontalElementDegrees
  rw [sourceControls_eq_blocks _ (by
    intro size member
    obtain ⟨element, elementMember, rfl⟩ := List.mem_map.mp member
    exact valid element elementMember), List.flatMap_map,
    UnaryFieldBooleanFilter.selectedValues_flatMap _ _ _ (by
      intro element member
      rw [List.length_map, sourceControlBlock_length _ (valid element member)]
      rfl)]
  have selected := List.flatMap_congr (fun element member =>
    selected_element_sources problem field element.1 element.2 (valid element member))
  refine selected.trans ?_
  simp only [horizontalElementPairs, PeriodicThreeDM.contractedEdges,
    PeriodicThreeDM.contractedEdgesForColor, List.flatMap_assoc, List.flatMap_map, List.map_flatMap]

end LeanTrominoes.PeriodicCNFStripReduction.CountedContractedIncidence
end
