/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListIdxOfLawfulBEq
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalIndexedAtomWordTargetListProjection
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceIncidenceAtomLookup
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceRouteDescriptorTargetVertexProjection

/-! # Copied-incidence target atom words -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicOrthocrossing

/-- The copied-incidence descriptor prefix emits the exact compact source-atom
word for every positional occurrence copy. -/
theorem occurrenceRouteDescriptorTargetAtomWords_eq_sourceAtomWords
    (source : PeriodicCNF (ThreeCNFVariable Nat)) :
    (RouteDescriptorTargetAtomWords.words
      (PeriodicThreeSATThree.occurrenceRouteDescriptors source)).words =
    (PeriodicThreeSATThree.allOccurrenceVariables source).map fun atom =>
      DirectSourceFinalIndexedAtomWords.word
        (PeriodicThreeSATThree.formula source)
        ⟨PeriodicPlanarSATVariable.atom atom⟩ := by
  apply indexedSourceAtomWords_eq_targetAtomWords
  · rw [PeriodicThreeSATThree.formula_variableOccurrences_dedup_eq_rotatedOccurrenceVariables]
    let descriptorBEq : BEq Variable :=
      @instBEqProd (ThreeCNFVariable Nat) (Nat × Nat)
        instBEqOfDecidableEq instBEqProd
    let sourceBEq : BEq Variable := instBEqProd
    have descriptorIndices :
        (PeriodicThreeSATThree.occurrenceRouteDescriptors source).map
            RouteDescriptor.targetVertexIndex =
          (PeriodicThreeSATThree.allOccurrenceVariables source).map
            (fun atom => @List.idxOf Variable descriptorBEq atom
              (PeriodicThreeSATThree.rotatedOccurrenceVariables source)) :=
      PeriodicThreeSATThree.occurrenceRouteDescriptors_targetVertexIndices
        source
    rw [descriptorIndices]
    apply List.map_congr_left
    intro atom _atomMember
    change @List.idxOf Variable descriptorBEq atom
        (PeriodicThreeSATThree.rotatedOccurrenceVariables source) =
      @List.idxOf Variable sourceBEq atom
        (PeriodicThreeSATThree.rotatedOccurrenceVariables source)
    exact listIdxOf_eq_of_lawfulBEq descriptorBEq sourceBEq
      inferInstance inferInstance atom _
  · intro atom atomMember
    rw [PeriodicThreeSATThree.formula_variableOccurrences_dedup_eq_rotatedOccurrenceVariables]
    exact
      (PeriodicThreeSATThree.mem_rotatedOccurrenceVariables_iff_allOccurrenceVariables
        source atom).mpr atomMember

end PeriodicCNFStripReduction
end LeanTrominoes

end
