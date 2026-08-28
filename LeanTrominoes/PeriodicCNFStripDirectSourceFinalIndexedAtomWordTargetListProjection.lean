/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalIndexedAtomWordTargetProjection

/-! # Descriptor target-index word streams -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicOrthocrossing
open PeriodicOrthocrossing.CarrierKeyWords

/-- Pointwise target-index agreement turns a descriptor stream into the exact
compact source-atom word stream. -/
theorem indexedSourceAtomWords_eq_targetAtomWords
    (source : PeriodicCNF Variable)
    (descriptors : List RouteDescriptor) (atoms : List Variable)
    (targetIndices :
      descriptors.map RouteDescriptor.targetVertexIndex =
        atoms.map fun atom =>
          source.variableOccurrences.dedup.idxOf atom)
    (atomsMember : ∀ atom ∈ atoms,
      atom ∈ source.variableOccurrences.dedup) :
    (RouteDescriptorTargetAtomWords.words descriptors).words =
      atoms.map fun atom =>
        DirectSourceFinalIndexedAtomWords.word source
          ⟨PeriodicPlanarSATVariable.atom atom⟩ := by
  have encodedIndices := congrArg
    (List.map fun index =>
      [true, false, false] ++ natField index)
    targetIndices
  rw [List.map_map, List.map_map] at encodedIndices
  have encodedIndices' :
      descriptors.map (fun descriptor =>
        [true, false, false] ++ natField descriptor.targetVertexIndex) =
      atoms.map (fun atom =>
        [true, false, false] ++
          natField (source.variableOccurrences.dedup.idxOf atom)) := by
    simpa only [Function.comp_def] using encodedIndices
  rw [show (RouteDescriptorTargetAtomWords.words descriptors).words =
      descriptors.map fun descriptor =>
        [true, false, false] ++ natField descriptor.targetVertexIndex by
      simp [RouteDescriptorTargetAtomWords.words,
        RouteDescriptorTargetAtomWords.word]]
  rw [encodedIndices']
  apply List.map_congr_left
  intro atom atomMember
  simp [DirectSourceFinalIndexedAtomWords.word,
    DirectSourceFinalIndexedAtomWords.sourceVariableWord,
    atomsMember atom atomMember]

end PeriodicCNFStripReduction
end LeanTrominoes

end
