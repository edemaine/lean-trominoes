/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkIncidenceSemantics

/-! # Global indices of occurrence-cycle incidences -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- Local cycle-suffix index `j` is global split-formula edge index `n + j`. -/
theorem cycleLinkIncidence_tagged_mem_formula
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (tagged : CNFIncidence (ThreeOccurrenceVariable Variable) × Nat)
    (taggedMember : tagged ∈ (cycleLinkIncidences source).zipIdx) :
    (tagged.1,
        PeriodicCNF.presentationLiteralCount source + tagged.2) ∈
      (PeriodicCNF.incidencesWithMetadata (formula source)).zipIdx := by
  have cycleLookup :=
    (List.mem_zipIdx_iff_getElem?).mp taggedMember
  apply (List.mem_zipIdx_iff_getElem?).mpr
  rw [formula_incidencesWithMetadata_eq_occurrence_append_cycle]
  rw [List.getElem?_append_right (by simp)]
  rw [occurrenceIncidences_length, Nat.add_sub_cancel_left]
  rw [← cycleLinkIncidences_eq_cycleIncidences]
  exact cycleLookup

end PeriodicThreeSATThree
end LeanTrominoes
