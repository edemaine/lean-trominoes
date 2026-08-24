/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceIncidenceTaggedAtomLookup
import LeanTrominoes.PeriodicThreeSATThreeRoutedVariableCycleTargetBlockLookup

/-! # Source route-descriptor lookup by positional occurrence atom -/

namespace LeanTrominoes.PeriodicThreeSATThree

/-- Target lookup at a genuine positional occurrence atom returns the route
descriptor copied from the corresponding source incidence. -/
theorem occurrenceRouteDescriptorAtOccurrenceAtom_eq_some
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : ThreeOccurrenceVariable Variable)
    (atomMember : atom ∈ rotatedOccurrenceVariables source) :
    ∃ taggedIncidence ∈
        (PeriodicCNF.incidencesWithMetadata source).zipIdx,
      occurrenceIncidenceAtAtom source atom =
          some (occurrenceIncidence taggedIncidence.1,
            taggedIncidence.2) ∧
        occurrenceRouteDescriptorAtTargetIndex source
            ((rotatedOccurrenceVariables source).idxOf atom) =
          some (occurrenceRouteDescriptor source
            taggedIncidence.1 taggedIncidence.2) := by
  have atomAllMember :=
    (mem_rotatedOccurrenceVariables_iff_allOccurrenceVariables
      source atom).mp atomMember
  rcases occurrenceIncidenceAtAtom_eq_some_tagged
      source atom atomAllMember with
    ⟨taggedIncidence, taggedMember, selectedAtom, semanticLookup⟩
  let descriptor := occurrenceRouteDescriptor source
    taggedIncidence.1 taggedIncidence.2
  have descriptorMember : descriptor ∈
      occurrenceRouteDescriptors source := by
    unfold descriptor occurrenceRouteDescriptors
    exact List.mem_map_of_mem taggedMember
  have targetEq : descriptor.targetVertexIndex =
      (rotatedOccurrenceVariables source).idxOf atom := by
    unfold descriptor occurrenceRouteDescriptor
    rw [← selectedAtom]
    rfl
  have descriptorLookup :
      occurrenceRouteDescriptorAtTargetIndex source
          ((rotatedOccurrenceVariables source).idxOf atom) =
        some descriptor := by
    rw [← targetEq]
    exact occurrenceRouteDescriptorAtTargetIndex_eq_some
      source descriptorMember
  exact ⟨taggedIncidence, taggedMember, semanticLookup,
    descriptorLookup⟩

end LeanTrominoes.PeriodicThreeSATThree
