/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.ListFilteredRankLookup
import LeanTrominoes.PeriodicOneInThreeToThreeDMOccurrences

/-! # Arbitrary tagged fields at a variable-slot presentation index -/

namespace LeanTrominoes.PeriodicOneInThreeToThreeDM

/-- A genuine variable-slot lookup selects every tagged field at the same
clause/literal presentation index, independently of the field's value type. -/
theorem taggedLiterals_map_getD_of_occurrenceAt
    {Variable Field : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable) (slot : OccurrenceSlot)
    (tagged : TaggedOccurrence Variable)
    (lookup : occurrenceAt source atom slot = some tagged)
    (field : TaggedOccurrence Variable → Field) (fallback : Field) :
    ((PeriodicThreeSATThree.taggedLiterals source).map field).getD
        ((source.variableOccurrences.idxsOf atom).getD slot.index 0) fallback =
      field tagged := by
  have filteredLookup : (occurrencesOf source atom)[slot.index]? = some tagged := lookup
  have rankLt := (List.getElem?_eq_some_iff.mp filteredLookup).1
  have selected := List.filter_map_getD_eq_atomIndices_getD
    (PeriodicThreeSATThree.taggedLiterals source) (fun item => item.1.atom) atom
    field fallback slot.index rankLt
  rw [taggedLiterals_atoms] at selected
  rw [← selected]
  change ((occurrencesOf source atom).map field).getD slot.index fallback = _
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, filteredLookup,
    Option.map_some, Option.getD_some]

end LeanTrominoes.PeriodicOneInThreeToThreeDM
