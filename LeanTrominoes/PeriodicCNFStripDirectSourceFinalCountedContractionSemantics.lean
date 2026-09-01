/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCanonicalElementCodeSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCanonicalElementDegreeSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCanonicalIncidenceElementCodeSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCountedContractionCompiler

/-! # Static promises of the direct final counted contraction -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The canonical element identity and degree columns are pointwise aligned. -/
theorem directSourceFinalCountedContraction_elementColumns_length
    (symbols : List encoding.Γ) :
    (directSourceFinalCanonicalElementCodes decider symbols).length =
      (directSourceFinalCanonicalElementDegrees decider symbols).length := by
  exact directSourceFinalCanonicalElementCodes_length decider symbols

/-- Every source degree meets the degree-two-or-degree-three promise of the
counted contraction table. -/
theorem directSourceFinalCountedContraction_degrees_valid
    (symbols : List encoding.Γ) :
    ∀ degree ∈ directSourceFinalCanonicalElementDegrees decider symbols,
      degree = 2 ∨ degree = 3 :=
  directSourceFinalCanonicalElementDegrees_valid decider symbols

/-- The incidence identity column is aligned one-for-one with the canonical
finite incidence queries underlying the direction-block stream. -/
theorem directSourceFinalCountedContraction_incidenceColumn_length
    (symbols : List encoding.Γ) :
    (directSourceFinalCanonicalIncidenceElementCodes
      decider symbols).length =
      (directSourceFinalCanonicalIncidenceQueries decider symbols).length := by
  exact directSourceFinalCanonicalIncidenceElementCodes_length decider symbols

end LeanTrominoes.PeriodicCNFStripReduction

end
