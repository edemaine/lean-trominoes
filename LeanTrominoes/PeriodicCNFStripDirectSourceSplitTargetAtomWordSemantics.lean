/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceCycleTargetAtomWordSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceOccurrenceTargetAtomWordSemantics

/-! # Complete occurrence-split target atom words -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicOrthocrossing

/-- The complete occurrence-split descriptor stream emits the copied source
atoms followed by the two cycle-incidence source atoms per occurrence. -/
theorem splitRouteDescriptorTargetAtomWords_eq_sourceAtomWords
    (source : PeriodicCNF (ThreeCNFVariable Nat)) :
    (RouteDescriptorTargetAtomWords.words
      (PeriodicThreeSATThree.splitRouteDescriptors source)).words =
    (PeriodicThreeSATThree.allOccurrenceVariables source).map
        (fun atom =>
          DirectSourceFinalIndexedAtomWords.word
            (PeriodicThreeSATThree.formula source)
            ⟨PeriodicPlanarSATVariable.atom atom⟩) ++
      ((PeriodicThreeSATThree.cycleLinkIncidences source).map
        (fun incidence => incidence.literal.atom)).map fun atom =>
          DirectSourceFinalIndexedAtomWords.word
            (PeriodicThreeSATThree.formula source)
            ⟨PeriodicPlanarSATVariable.atom atom⟩ := by
  rw [show PeriodicThreeSATThree.splitRouteDescriptors source =
      PeriodicThreeSATThree.occurrenceRouteDescriptors source ++
        PeriodicThreeSATThree.cycleLinkRouteDescriptors source by rfl]
  simpa only [RouteDescriptorTargetAtomWords.words, List.map_append] using
    congrArg₂ (fun first second => first ++ second)
      (occurrenceRouteDescriptorTargetAtomWords_eq_sourceAtomWords source)
      (cycleLinkRouteDescriptorTargetAtomWords_eq_sourceAtomWords source)

end PeriodicCNFStripReduction
end LeanTrominoes

end
