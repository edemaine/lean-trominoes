/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseFamilies
import LeanTrominoes.PeriodicCNFStripDirectSourceNormalizedFormula

/-! # Global starts of the final direct-source clause families -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalClauseFamilyStartsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The unguarded occurrence-split formula underlying every named final
clause family. -/
def directSourceFinalNormalizedFormula
    (symbols : List encoding.Γ) : PeriodicCNF Variable :=
  PeriodicThreeSATThree.formula
    (directThreeCNFSourceFormula decider symbols)

theorem directSourceFormula_eq_finalNormalized
    (symbols : List encoding.Γ) :
    directSourceFormula decider symbols =
      directSourceFinalNormalizedFormula decider symbols := by
  unfold directSourceFinalNormalizedFormula directThreeCNFSourceFormula
  exact directSourceFormula_eq_threeSATThree decider symbols

/-- The carrier family follows the crossover prefix. -/
def directSourceFinalCarrierStart
    (symbols : List encoding.Γ) : Nat :=
  (directSourceFinalCrossoverClauses decider symbols).length

/-- The bend family follows crossovers and retained carriers. -/
def directSourceFinalBendStart
    (symbols : List encoding.Γ) : Nat :=
  directSourceFinalCarrierStart decider symbols +
    (directSourceFinalCarrierClauses decider symbols).length

/-- The routed-clause family follows crossovers, carriers, and bends. -/
def directSourceFinalRoutedClauseStart
    (symbols : List encoding.Γ) : Nat :=
  directSourceFinalBendStart decider symbols +
    (directSourceFinalBendClauses decider symbols).length

/-- The routed-variable family is the final clause-family suffix. -/
def directSourceFinalRoutedVariableStart
    (symbols : List encoding.Γ) : Nat :=
  directSourceFinalRoutedClauseStart decider symbols +
    (directSourceFinalRoutedClauseClauses decider symbols).length

end LeanTrominoes.PeriodicCNFStripReduction

end
