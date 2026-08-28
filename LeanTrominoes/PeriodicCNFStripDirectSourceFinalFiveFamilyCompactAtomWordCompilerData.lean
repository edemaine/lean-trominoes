/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordsAppendClosure
import LeanTrominoes.PeriodicCNFStripDirectSourceBendCompactAtomWordBlockSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierCompactAtomWordBlockSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceCrossoverCompactAtomWordBlockSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceRoutedClauseCompactAtomWordSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceRoutedVariableCompactAtomWordSemantics

/-! # Append tree for the five final compact atom-word families -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFiveFamilyCompactDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The first two final compact word families. -/
def directSourceFinalCompactCrossoverCarrierAtomWords
    (symbols : List encoding.Γ) : DelimitedBinaryWords.Input :=
  DelimitedBinaryWords.append
    (directSourceFinalCompactCrossoverAtomWords decider symbols)
    (directSourceFinalCompactCarrierAtomWords decider symbols)

/-- The bend and routed-clause compact word families. -/
def directSourceFinalCompactBendRoutedClauseAtomWords
    (symbols : List encoding.Γ) : DelimitedBinaryWords.Input :=
  DelimitedBinaryWords.append
    (directSourceFinalCompactBendAtomWords decider symbols)
    (directSourceFinalCompactRoutedClauseAtomWords decider symbols)

/-- The final three compact word families. -/
def directSourceFinalCompactBendRoutedSuffixAtomWords
    (symbols : List encoding.Γ) : DelimitedBinaryWords.Input :=
  DelimitedBinaryWords.append
    (directSourceFinalCompactBendRoutedClauseAtomWords decider symbols)
    (directSourceFinalRoutedVariableCompactAtomWords decider symbols)

/-- All five final compact atom-word families, preserving the semantic
append tree of the duplicate-free final occurrence presentation. -/
def directSourceFinalFiveFamilyCompiledCompactAtomWords
    (symbols : List encoding.Γ) : DelimitedBinaryWords.Input :=
  DelimitedBinaryWords.append
    (directSourceFinalCompactCrossoverCarrierAtomWords decider symbols)
    (directSourceFinalCompactBendRoutedSuffixAtomWords decider symbols)

end PeriodicCNFStripReduction
end LeanTrominoes

end
