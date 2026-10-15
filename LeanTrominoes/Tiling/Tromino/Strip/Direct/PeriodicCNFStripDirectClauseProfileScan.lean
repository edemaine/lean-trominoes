/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFPolySpaceRequestEmitter
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectClauseArityScan
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFUnaryProgramClauseProfileCompiler
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFUnaryProgramClauseProfileSemantics

/-! # Exact finite clause profiles for the direct strip reduction -/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace StripDirectClauseProfileScan

open UnaryProgramClauseProfile

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)

def sourceClauseProfiles (symbols : List encoding.Γ) :
    List ClauseProfile :=
  requestScan (ProgramSource.sourceTokens decider symbols)

noncomputable def sourceClauseProfilesComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List ClauseProfile)
      encoding.Γ ClauseProfile id id
      (sourceClauseProfiles decider) := by
  let complete := TM2CompositionMachine.computableInPolyTime
    (ProgramSource.sourceTokensComputableInPolyTime decider)
    requestScanComputableInPolyTime
  exact complete

/-- The richer stream projects exactly to the previously verified arity
stream. -/
@[simp] theorem sourceClauseProfiles_map_arity
    (symbols : List encoding.Γ) :
    (sourceClauseProfiles decider symbols).map ClauseProfile.arity =
      StripDirectClauseArityScan.sourceClauseArities decider symbols := by
  unfold sourceClauseProfiles
    StripDirectClauseArityScan.sourceClauseArities
  exact requestScan_map_arity _

/-- The source profile stream contains exactly every generated literal's
polarity and current/next-slice offset, in formula clause order. -/
theorem sourceClauseProfiles_literals_eq_formula
    (symbols : List encoding.Γ) :
    (sourceClauseProfiles decider symbols).map ClauseProfile.literals =
      (ProgramSource.formulaOfSymbols decider symbols).clauses.map
        (List.map LiteralProfile.ofLiteral) := by
  unfold sourceClauseProfiles
  rw [ProgramSource.sourceTokens_eq_requestSource]
  rw [requestScan_literals_eq_clauseProfiles]
  rw [ProgramSource.formula_eq]

end StripDirectClauseProfileScan
end PeriodicCNF
end LeanTrominoes
