/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Formula.PeriodicCNFStripDirectSourceFormulaFacts
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFPolySpaceCompiler

/-! # Named direct strip source formulas -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- The normalized source formula generated directly from an encoded input. -/
def directSourceFormula (symbols : List encoding.Γ) :
    PeriodicCNF Variable :=
  sourceFormula (ProgramSource.formulaOfSymbols decider symbols)

/-- Shared canonical equality implementation for direct source variables.
Naming it keeps independently compiled semantic leaves definitionally aligned. -/
noncomputable def directSourceVariableDecidableEq : DecidableEq Variable :=
  Classical.decEq _

@[reducible] noncomputable def directSourceVariableBEq : BEq Variable :=
  @instBEqOfDecidableEq Variable directSourceVariableDecidableEq

theorem directSourceVariableLawfulBEq :
    @LawfulBEq Variable directSourceVariableBEq := by
  unfold directSourceVariableBEq directSourceVariableDecidableEq
  infer_instance

end PeriodicCNFStripReduction
end LeanTrominoes
