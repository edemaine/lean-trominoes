/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripCountedContractedIncidenceSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCountedContractionSemantics

/-! # Exact contraction plan of the direct final source -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The direct source's compiled query keys are exactly the two- or
three-incidence block attached to every canonical element, in element-major
order. -/
theorem directSourceFinalCountedContraction_queryKeys_eq
    (symbols : List encoding.Γ) :
    CountedContractedIncidence.queryKeys
        (directSourceFinalCanonicalElementCodes decider symbols)
        (directSourceFinalCanonicalElementDegrees decider symbols) =
      (List.zipWith CountedContractedIncidence.queryBlock
        (directSourceFinalCanonicalElementCodes decider symbols)
        (directSourceFinalCanonicalElementDegrees decider symbols)).flatten := by
  exact CountedContractedIncidence.queryKeys_eq_zipWith
    (directSourceFinalCanonicalElementCodes decider symbols)
    (directSourceFinalCanonicalElementDegrees decider symbols)
    (directSourceFinalCountedContraction_elementColumns_length
      decider symbols)
    (directSourceFinalCountedContraction_degrees_valid decider symbols)

/-- The aligned role stream is exactly one through pair for every
degree-two element and three retained roles for every degree-three element. -/
theorem directSourceFinalCountedContraction_roles_eq
    (symbols : List encoding.Γ) :
    CountedContractedIncidence.roles
        (directSourceFinalCanonicalElementDegrees decider symbols) =
      ((directSourceFinalCanonicalElementDegrees decider symbols).map
        CountedContractedIncidence.expectedRoleBlock).flatten := by
  exact CountedContractedIncidence.roles_eq_map
    (directSourceFinalCanonicalElementDegrees decider symbols)
    (directSourceFinalCountedContraction_degrees_valid decider symbols)

/-- The independently compiled incidence identities become precisely their
stable base-three occurrence keys before keyed block selection. -/
theorem directSourceFinalCountedContraction_incidenceBlockKeys_eq
    (symbols : List encoding.Γ) :
    CountedContractedIncidence.incidenceBlockKeys
        (directSourceFinalCanonicalIncidenceElementCodes decider symbols) =
      StableOccurrenceRanks.candidateKeys
        (directSourceFinalCanonicalIncidenceElementCodes decider symbols) := by
  exact CountedContractedIncidence.incidenceBlockKeys_eq_candidateKeys _

end LeanTrominoes.PeriodicCNFStripReduction

end
