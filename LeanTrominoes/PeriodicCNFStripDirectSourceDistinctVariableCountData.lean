/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaData

/-! # Named direct-source distinct-variable counts -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceDistinctVariableCountStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- A shared equality-decider-independent name for the direct source's number
of distinct variables. -/
def directSourceDistinctVariableCount (symbols : List encoding.Γ) : Nat :=
  (@List.dedup Variable directSourceVariableDecidableEq
    (directSourceFormula decider symbols).variableOccurrences).length

end PeriodicCNFStripReduction
end LeanTrominoes

end
