/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Zero.PeriodicCNFStripDirectSourceZeroAnchors
import LeanTrominoes.SAT.ThreeSAT.PeriodicThreeCNFFormulaZeroAnchors

/-! # Zero anchors after direct width-three conversion -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Width-three conversion preserves the direct transition program's
current-slice clause anchors. -/
theorem directThreeCNFSource_zeroAnchored
    (symbols : List encoding.Γ) :
    (PeriodicThreeCNF.formula
      (PeriodicCNF.ProgramSource.formulaOfSymbols
        decider symbols)).IsZeroAnchored := by
  exact PeriodicThreeCNF.formula_zeroAnchored _
    (formulaOfSymbols_zeroAnchored decider symbols)

end PeriodicCNFStripReduction
end LeanTrominoes
