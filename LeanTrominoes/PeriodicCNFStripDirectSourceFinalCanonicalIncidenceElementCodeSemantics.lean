/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCanonicalIncidenceElementCodeCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCanonicalIncidenceKeySemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseIncidenceElementCodeSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableIncidenceElementCodeSemantics

/-! # Semantics of the complete incidence element-code column -/

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- There is exactly one element identity per canonical incidence query and
therefore per independently delimited direction block. -/
@[simp] theorem directSourceFinalCanonicalIncidenceElementCodes_length
    (symbols : List encoding.Γ) :
    (directSourceFinalCanonicalIncidenceElementCodes
      decider symbols).length =
      (directSourceFinalCanonicalIncidenceQueries decider symbols).length := by
  simp [directSourceFinalCanonicalIncidenceElementCodes,
    directSourceFinalCanonicalIncidenceQueries]

end LeanTrominoes.PeriodicCNFStripReduction
