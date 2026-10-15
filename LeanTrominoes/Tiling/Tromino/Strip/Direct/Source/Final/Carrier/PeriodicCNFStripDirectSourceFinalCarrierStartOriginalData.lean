/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Carrier.PeriodicCNFStripDirectSourceFinalCarrierStartFamilyData

/-! # Original equality-parameterized final-carrier start -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- The original crossover-prefix computation hidden behind a small name. -/
def directSourceFinalCarrierOriginalStart
    (symbols : List encoding.Γ) : Nat :=
  directSourceFinalCarrierStartFamily decider symbols
    directSourceVariableDecidableEq

end LeanTrominoes.PeriodicCNFStripReduction

end
