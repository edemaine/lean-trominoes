/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListIdxOfLawfulBEq
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalIndexedAtomWordTargetListProjection
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkIncidenceAtomDedup
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkRouteDescriptorTargetVertexProjection
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceIncidenceAtomLookup

/-! # Cycle-incidence target atom words -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicOrthocrossing

/-- The cycle-link descriptor suffix emits the exact compact source-atom word
of each implication-cycle incidence. -/
theorem cycleLinkRouteDescriptorTargetAtomWords_eq_sourceAtomWords
    (source : PeriodicCNF (ThreeCNFVariable Nat)) :
    (RouteDescriptorTargetAtomWords.words
      (PeriodicThreeSATThree.cycleLinkRouteDescriptors source)).words =
    ((PeriodicThreeSATThree.cycleLinkIncidences source).map
      (fun incidence => incidence.literal.atom)).map fun atom =>
        DirectSourceFinalIndexedAtomWords.word
          (PeriodicThreeSATThree.formula source)
          ⟨PeriodicPlanarSATVariable.atom atom⟩ := by
  apply indexedSourceAtomWords_eq_targetAtomWords
  · rw [PeriodicThreeSATThree.formula_variableOccurrences_dedup_eq_rotatedOccurrenceVariables]
    let descriptorBEq : BEq Variable := instBEqOfDecidableEq
    let sourceBEq : BEq Variable := instBEqProd
    have descriptorIndices :
        (PeriodicThreeSATThree.cycleLinkRouteDescriptors source).map
            RouteDescriptor.targetVertexIndex =
          ((PeriodicThreeSATThree.cycleLinkIncidences source).map
            (fun incidence => incidence.literal.atom)).map
              (fun atom => @List.idxOf Variable descriptorBEq atom
                (PeriodicThreeSATThree.rotatedOccurrenceVariables source)) :=
      PeriodicThreeSATThree.cycleLinkRouteDescriptors_targetVertexIndices_eq_atomStream
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
    apply
      (PeriodicThreeSATThree.mem_rotatedOccurrenceVariables_iff_allOccurrenceVariables
        source atom).mpr
    exact
      (PeriodicThreeSATThree.mem_cycleLinkIncidenceAtoms_iff
        source atom).mp atomMember

end PeriodicCNFStripReduction
end LeanTrominoes

end
