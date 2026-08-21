/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorFacts
import LeanTrominoes.PeriodicThreeSATThreeExactOccurrences

/-! # Target-port rank bounds after occurrence splitting -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- Every occurrence-copy variable appears on exactly three routes, so the
rank of a genuine route at its variable endpoint is one of `0`, `1`, or `2`. -/
theorem numericRouteDescriptor_formula_targetPortRank_lt_three
    {Variable : Type*} [DecidableEq Variable]
    [DecidableEq (ThreeOccurrenceVariable Variable)]
    (source : PeriodicCNF Variable)
    (tagged : CNFIncidence (ThreeOccurrenceVariable Variable) × Nat)
    (taggedMember : tagged ∈
      (PeriodicCNF.incidencesWithMetadata (formula source)).zipIdx) :
    (tagged.1.numericRouteDescriptor
      (formula source) tagged.2).targetPortRank < 3 := by
  let occurrences :=
    PeriodicCNF.variableOccurrences (formula source)
  have metadataLookup :=
    (List.mem_zipIdx_iff_getElem?).mp taggedMember
  have occurrenceLookup :
      occurrences[tagged.2]? = some tagged.1.literal.atom := by
    dsimp [occurrences]
    rw [← PeriodicCNF.incidencesWithMetadata_atoms]
    rw [List.getElem?_map, metadataLookup]
    rfl
  have indexLt : tagged.2 < occurrences.length :=
    (List.getElem?_eq_some_iff.mp occurrenceLookup).1
  have occurrenceEq :
      occurrences[tagged.2] = tagged.1.literal.atom :=
    (List.getElem?_eq_some_iff.mp occurrenceLookup).2
  have atomMember :=
    PeriodicCNF.metadataIncidence_atom_mem_dedup
      (formula source) tagged taggedMember
  have totalCount :
      @List.count (ThreeOccurrenceVariable Variable)
          instBEqOfDecidableEq tagged.1.literal.atom occurrences = 3 :=
    formula_variableOccurrences_count_eq_three_of_mem_with_beq
      instBEqOfDecidableEq (by infer_instance)
      source tagged.1.literal.atom atomMember
  have prefixBound :=
    @List.count_getElem_take_lt_count
      (ThreeOccurrenceVariable Variable) instBEqOfDecidableEq
      (by infer_instance) occurrences tagged.2 indexLt
  rw [occurrenceEq, totalCount] at prefixBound
  exact prefixBound

end PeriodicThreeSATThree
end LeanTrominoes
