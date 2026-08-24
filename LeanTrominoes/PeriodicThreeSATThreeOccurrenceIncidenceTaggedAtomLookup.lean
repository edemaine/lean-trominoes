/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceIncidenceAtomLookup

/-! # Source-incidence lookup by positional occurrence atom -/

namespace LeanTrominoes.PeriodicThreeSATThree

/-- The copied-incidence enumeration is the source-incidence enumeration
with each incidence replaced by its positional occurrence copy. -/
theorem occurrenceIncidences_zipIdx_eq_map
    {Variable : Type*} (source : PeriodicCNF Variable) :
    (occurrenceIncidences source).zipIdx =
      (PeriodicCNF.incidencesWithMetadata source).zipIdx.map
        (fun taggedIncidence =>
          (occurrenceIncidence taggedIncidence.1,
            taggedIncidence.2)) := by
  unfold occurrenceIncidences
  rw [List.zipIdx_map]
  rfl

/-- A genuine positional occurrence atom comes from a source incidence,
and its semantic copied-incidence lookup returns that source incidence's
positional copy with the same global index. -/
theorem occurrenceIncidenceAtAtom_eq_some_tagged
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : ThreeOccurrenceVariable Variable)
    (atomMember : atom ∈ allOccurrenceVariables source) :
    ∃ taggedIncidence ∈
        (PeriodicCNF.incidencesWithMetadata source).zipIdx,
      (occurrenceIncidence taggedIncidence.1).literal.atom = atom ∧
        occurrenceIncidenceAtAtom source atom =
          some (occurrenceIncidence taggedIncidence.1,
            taggedIncidence.2) := by
  rcases occurrenceIncidenceAtAtom_eq_some
      source atom atomMember with
    ⟨selected, selectedMember, selectedAtom, semanticLookup⟩
  rw [occurrenceIncidences_zipIdx_eq_map] at selectedMember
  rcases List.mem_map.mp selectedMember with
    ⟨taggedIncidence, taggedMember, selectedEq⟩
  subst selected
  exact ⟨taggedIncidence, taggedMember, selectedAtom, semanticLookup⟩

end LeanTrominoes.PeriodicThreeSATThree
