/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceCrossoverCompactAtomWordFinalSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCompactOccurrenceAtomWordFamilies

/-! # Direct crossover words at the final five-family boundary -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directCrossoverBlockSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directCrossoverBlockSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The direct semantic target is exactly the crossover block named by the
final five-family compact occurrence presentation. -/
theorem directSourceFinalCompactCrossoverAtomWords_eq_block
    (symbols : List encoding.Γ) :
    directSourceFinalCompactCrossoverAtomWords decider symbols =
      ⟨directSourceFinalCompactCrossoverAtomWordBlock decider symbols⟩ := by
  unfold directSourceFinalCompactCrossoverAtomWords
    directSourceFinalCompactCrossoverAtomWordBlock
    directThreeCNFSourceFormula
    directSourceFinalCompactAtomWord
  rw [directSourceFormula_eq_threeSATThree]

end PeriodicCNFStripReduction
end LeanTrominoes

end
