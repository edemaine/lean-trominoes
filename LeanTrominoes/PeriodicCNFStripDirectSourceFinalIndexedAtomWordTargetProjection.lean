/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalIndexedAtomWord
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorTargetAtomWordData

/-! # Indexed source-atom words from descriptor target indices -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicOrthocrossing
open PeriodicOrthocrossing.CarrierKeyWords

/-- A descriptor naming an actual source variable by its deduplicated vertex
index emits exactly that variable's compact final atom word. -/
theorem indexedSourceAtomWord_eq_targetAtomWord
    (source : PeriodicCNF Variable)
    (atom : Variable) (descriptor : RouteDescriptor)
    (atomMember : atom ∈ source.variableOccurrences.dedup)
    (targetEq : descriptor.targetVertexIndex =
      source.variableOccurrences.dedup.idxOf atom) :
    DirectSourceFinalIndexedAtomWords.word source
        ⟨PeriodicPlanarSATVariable.atom atom⟩ =
      RouteDescriptorTargetAtomWords.word descriptor := by
  have rawMember : atom ∈ source.variableOccurrences :=
    List.mem_dedup.mp atomMember
  simp [DirectSourceFinalIndexedAtomWords.word,
    DirectSourceFinalIndexedAtomWords.sourceVariableWord,
    RouteDescriptorTargetAtomWords.word, rawMember, targetEq]

end PeriodicCNFStripReduction
end LeanTrominoes

end
