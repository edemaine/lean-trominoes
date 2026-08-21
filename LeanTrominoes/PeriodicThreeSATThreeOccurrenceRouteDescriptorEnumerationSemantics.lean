/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.IndexedListMapIndices
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorEnumerationData
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceIncidencePrefix
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceRouteDescriptorEnumerationData
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceRouteDescriptorSemantics

/-! # Correctness of the copied route-descriptor enumeration -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- The first `n` semantic numeric route records are exactly the explicit
copied-source records. -/
theorem numericRouteDescriptors_formula_take_sourceCount
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (PeriodicCNF.numericRouteDescriptors (formula source)).take
        (PeriodicCNF.presentationLiteralCount source) =
      occurrenceRouteDescriptors source := by
  have liftedIndices :
      (occurrenceIncidences source).zipIdx =
        (PeriodicCNF.incidencesWithMetadata source).zipIdx.map
          (fun tagged =>
            (occurrenceIncidence tagged.1, tagged.2)) := by
    unfold occurrenceIncidences
    rw [List.zipIdx_map]
    apply List.map_congr_left
    intro tagged taggedMember
    cases tagged
    rfl
  unfold PeriodicCNF.numericRouteDescriptors
  rw [← List.map_take]
  rw [List.take_zipIdx]
  rw [formula_incidencesWithMetadata_take_sourceCount]
  rw [liftedIndices, List.map_map]
  unfold occurrenceRouteDescriptors
  apply List.map_congr_left
  intro tagged taggedMember
  exact occurrenceIncidence_numericRouteDescriptor_eq
    source tagged taggedMember

end PeriodicThreeSATThree
end LeanTrominoes
