/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Canonical.PeriodicCNFStripDirectSourceFinalCanonicalIncidenceElementCodeCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Canonical.PeriodicCNFStripDirectSourceFinalCanonicalIncidenceKeySemantics
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Clause.PeriodicCNFStripDirectSourceFinalClauseIncidenceElementCodeSemantics
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Variable.PeriodicCNFStripDirectSourceFinalVariableIncidenceElementCodeSemantics

/-! # Semantics of the complete incidence element-code column -/

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)

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
