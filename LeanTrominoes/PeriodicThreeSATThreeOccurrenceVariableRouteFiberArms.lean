/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarVariablePortGeometry
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceIncidenceRanks
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceVariableRouteFiberSelection

/-! # Numeric target arms in copied-occurrence route fibers -/

namespace LeanTrominoes.PeriodicThreeSATThree

open PeriodicOrthocrossing PlanarThreeSAT

/-- The copied-incidence prefix contributes its left target arm exactly at
the neighboring translates of the selected incidence. -/
theorem occurrenceIncidenceFiberNumericArmsAt_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (selected : CNFIncidence (ThreeOccurrenceVariable Variable) × Nat)
    (selectedMember : selected ∈ (occurrenceIncidences source).zipIdx)
    (position : Cell) :
    (((occurrenceIncidences source).zipIdx.flatMap
        fun taggedIncidence =>
          translatedIncidenceOccurrencesAt taggedIncidence
            (selected.1.literal.atom, position)).map
        (fun occurrence =>
          targetDuplicatorArm
            (occurrence.incidence.numericRouteDescriptor
              (formula source) occurrence.edgeIndex).targetPortRank)) =
      if Cell.sub position selected.1.edge.offset ∈ neighborTranslations then
        [.left]
      else
        [] := by
  rw [occurrenceIncidenceFibersAt_eq_selected
    source selectedMember position]
  rw [selectedOccurrenceIncidenceFiber_eq]
  by_cases translateMember :
      Cell.sub position selected.1.edge.offset ∈ neighborTranslations
  · rw [if_pos translateMember, if_pos translateMember]
    simp only [List.map_cons, List.map_nil]
    rw [occurrenceIncidence_numericRouteDescriptor_targetPortRank
      source selected selectedMember]
    rfl
  · rw [if_neg translateMember, if_neg translateMember]
    rfl

end LeanTrominoes.PeriodicThreeSATThree
