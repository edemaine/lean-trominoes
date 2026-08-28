/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaData

/-! # Shared reducible equality instance for direct-source variables -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

/-- A reducible instance spelling for the canonical direct-source variable
equality.  Semantic and compiler leaves can locally register this same
constant and remain definitionally aligned. -/
@[reducible] noncomputable def directSourceVariableDecidableEqInstance :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

end LeanTrominoes.PeriodicCNFStripReduction

end
