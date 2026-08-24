/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListFindUnique
import LeanTrominoes.ListZipIdxFstMembership
import LeanTrominoes.PeriodicThreeSATThreeVariableRouteSiteArmBlocks

/-! # Copied-incidence lookup by positional occurrence atom -/

namespace LeanTrominoes.PeriodicThreeSATThree

/-- Rotating within source-variable occurrence groups preserves membership. -/
theorem mem_rotatedOccurrenceVariables_iff_allOccurrenceVariables
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : ThreeOccurrenceVariable Variable) :
    atom ∈ rotatedOccurrenceVariables source ↔
      atom ∈ allOccurrenceVariables source := by
  rw [← cycleLinkIncidences_atoms_dedup_eq_rotatedOccurrenceVariables,
    List.mem_dedup, mem_cycleLinkIncidenceAtoms_iff]

/-- Lookup by a genuine positional occurrence atom returns its unique copied
incidence and global copied-prefix index. -/
theorem occurrenceIncidenceAtAtom_eq_some
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : ThreeOccurrenceVariable Variable)
    (atomMember : atom ∈ allOccurrenceVariables source) :
    ∃ selected ∈ (occurrenceIncidences source).zipIdx,
      selected.1.literal.atom = atom ∧
        occurrenceIncidenceAtAtom source atom = some selected := by
  have incidenceAtomMember : atom ∈
      (occurrenceIncidences source).map
        (fun incidence => incidence.literal.atom) := by
    simpa [occurrenceIncidences_atoms] using atomMember
  rcases List.mem_map.mp incidenceAtomMember with
    ⟨incidence, incidenceMember, incidenceAtom⟩
  rcases exists_mem_zipIdx_fst
      (occurrenceIncidences source) 0 incidenceMember with
    ⟨index, selectedMember⟩
  let selected := (incidence, index)
  have selectedAtom : selected.1.literal.atom = atom := incidenceAtom
  have keysNodup :
      (((occurrenceIncidences source).zipIdx).map fun taggedIncidence =>
        taggedIncidence.1.literal.atom).Nodup := by
    have keysEq :
        ((occurrenceIncidences source).zipIdx).map
            (fun taggedIncidence => taggedIncidence.1.literal.atom) =
          (occurrenceIncidences source).map
            (fun incidence => incidence.literal.atom) := by
      calc
        _ = (((occurrenceIncidences source).zipIdx).map Prod.fst).map
              (fun incidence => incidence.literal.atom) := by
            rw [List.map_map]
            apply List.map_congr_left
            intro taggedIncidence _taggedMember
            rfl
        _ = _ := by rw [List.zipIdx_map_fst]
    rw [keysEq, occurrenceIncidences_atoms]
    exact allOccurrenceVariables_nodup source
  have lookup : occurrenceIncidenceAtAtom source atom = some selected := by
    unfold occurrenceIncidenceAtAtom
    apply listFind?_eq_some_of_mem_of_unique
      (occurrenceIncidences source).zipIdx
      (fun taggedIncidence =>
        decide (taggedIncidence.1.literal.atom = atom))
      selected selectedMember
    · simp [selectedAtom]
    · intro candidate candidateMember candidateTrue
      apply List.inj_on_of_nodup_map keysNodup
        candidateMember selectedMember
      have candidateAtom : candidate.1.literal.atom = atom := by
        exact of_decide_eq_true candidateTrue
      exact candidateAtom.trans selectedAtom.symm
  exact ⟨selected, selectedMember, selectedAtom, lookup⟩

end LeanTrominoes.PeriodicThreeSATThree
