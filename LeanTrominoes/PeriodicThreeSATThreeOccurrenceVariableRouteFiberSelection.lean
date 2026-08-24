/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListFlatMapUniqueKey
import LeanTrominoes.PeriodicCNFPlanarRouteOccurrenceFiberSemantics
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceIncidenceAtoms

/-! # Unique copied-incidence fiber at one occurrence variable -/

namespace LeanTrominoes.PeriodicThreeSATThree

open PeriodicOrthocrossing

/-- In the copied-incidence prefix, the site of one positional variable can
receive only that variable's unique copied incidence. -/
theorem occurrenceIncidenceFibersAt_eq_selected
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    {selected : CNFIncidence (ThreeOccurrenceVariable Variable) × Nat}
    (selectedMember : selected ∈ (occurrenceIncidences source).zipIdx)
    (position : Cell) :
    ((occurrenceIncidences source).zipIdx.flatMap fun taggedIncidence =>
        translatedIncidenceOccurrencesAt taggedIncidence
          (selected.1.literal.atom, position)) =
      translatedIncidenceOccurrencesAt selected
        (selected.1.literal.atom, position) := by
  have atomKeysNodup :
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
  apply flatMap_eq_selected_of_key_nodup
    (occurrenceIncidences source).zipIdx
    (fun taggedIncidence => taggedIncidence.1.literal.atom)
    atomKeysNodup
    (fun taggedIncidence =>
      translatedIncidenceOccurrencesAt taggedIncidence
        (selected.1.literal.atom, position))
    selected selectedMember
  intro taggedIncidence _taggedMember differentAtom
  rw [translatedIncidenceOccurrencesAt_eq]
  simp [differentAtom]

/-- The selected copied incidence contributes its unique translated
occurrence exactly when `position - offset` is neighboring. -/
theorem selectedOccurrenceIncidenceFiber_eq
    {Variable : Type*} [DecidableEq Variable]
    (selected : CNFIncidence (ThreeOccurrenceVariable Variable) × Nat)
    (position : Cell) :
    translatedIncidenceOccurrencesAt selected
        (selected.1.literal.atom, position) =
      let translate := Cell.sub position selected.1.edge.offset
      if translate ∈ neighborTranslations then
        [⟨selected.1, selected.2, translate⟩]
      else
        [] := by
  rw [translatedIncidenceOccurrencesAt_eq]
  simp

end LeanTrominoes.PeriodicThreeSATThree
