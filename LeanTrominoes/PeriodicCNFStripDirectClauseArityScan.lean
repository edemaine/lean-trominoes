/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFPolySpaceRequestEmitter
import LeanTrominoes.PeriodicCNFUnaryProgramClauseArityCompiler
import LeanTrominoes.PeriodicCNFUnaryProgramClauseAritySemantics

/-!
# Exact clause-arity stream for the direct strip reduction

This leaf connects the finite clause-arity scan to the concrete source-symbol
printer used by the polynomial-space reduction.
-/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace StripDirectClauseArityScan

open UnaryProgramClauseArity

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)

def sourceClauseArities (symbols : List encoding.Γ) : List Arity :=
  requestScan (ProgramSource.sourceTokens decider symbols)

/-- Exact clause arities can be extracted directly from the finite source
alphabet in polynomial time. -/
noncomputable def sourceClauseAritiesComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List Arity) encoding.Γ Arity id id
      (sourceClauseArities decider) := by
  let complete := TM2CompositionMachine.computableInPolyTime
    (ProgramSource.sourceTokensComputableInPolyTime decider)
    requestScanComputableInPolyTime
  exact complete

/-- Interpreting the finite arity tags gives the clause lengths of the exact
periodic CNF produced by the source-symbol compiler. -/
theorem sourceClauseArities_values_eq_clauseLengths
    (symbols : List encoding.Γ) :
    (sourceClauseArities decider symbols).map Arity.value =
      (ProgramSource.formulaOfSymbols decider symbols).clauses.map
        List.length := by
  unfold sourceClauseArities
  rw [ProgramSource.sourceTokens_eq_requestSource]
  rw [requestScan_values_eq_clauseLengths]
  rw [ProgramSource.formula_eq]

end StripDirectClauseArityScan
end PeriodicCNF
end LeanTrominoes
