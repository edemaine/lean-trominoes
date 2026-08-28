/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairBooleanFilterData
import LeanTrominoes.DelimitedBinaryWordPairProductMachine
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierCompactAtomWordStreamData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalEnumerationData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedRetainedPairData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierRankDatumData

/-! # Retained direct-source compact carrier word pairs -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directCarrierCompactPairStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

attribute [local instance] directSourceVariableDecidableEqInstance

/-- One exact compact carrier atom word per global stable carrier rank. -/
def directSourceCarrierCompactAtomWords
    (symbols : List encoding.Γ) : DelimitedBinaryWords.Input :=
  let formula := directSourceFormula decider symbols
  let descriptors := numericRouteDescriptors formula
  let period := routeDescriptorStreamGridSize descriptors
  let datums :=
    (routeDescriptorCarrierRankDatumsAtPeriod period descriptors).dedup
  let nodes := (CarrierRankGlobal.enumeration datums).map
    (fun entry => entry.1.identity.node)
  GuardedCarrierSourcePairCompactAtomWords.wordsAtPeriod period nodes

/-- Row-major square of globally ranked compact carrier atom words. -/
def directSourceCarrierCompactAtomWordPairs
    (symbols : List encoding.Γ) : DelimitedBinaryWordPairs.Input :=
  DelimitedBinaryWordPairProductMachine.pairs
    (directSourceCarrierCompactAtomWords decider symbols)

/-- The exact global-rank mask selecting retained adjacent carrier links. -/
def directSourceCarrierRetainedPairMask
    (symbols : List encoding.Γ) : List Bool :=
  CarrierRankOrderedPairs.retainedMaskBits
    (numericRouteDescriptors (directSourceFormula decider symbols))

/-- The direct compact carrier-word square filtered positionally by the
retained-pair mask. -/
def directSourceCarrierSelectedCompactAtomWordPairs
    (symbols : List encoding.Γ) : DelimitedBinaryWordPairs.Input :=
  ⟨DelimitedBinaryWordPairBooleanFilter.selectedPairs
    (directSourceCarrierRetainedPairMask decider symbols)
    (directSourceCarrierCompactAtomWordPairs decider symbols).pairs⟩

theorem directSourceCarrierSelectedCompactAtomWordPairs_eq_selected
    (symbols : List encoding.Γ) :
    directSourceCarrierSelectedCompactAtomWordPairs decider symbols =
      ⟨DelimitedBinaryWordPairBooleanFilter.selectedPairs
        (directSourceCarrierRetainedPairMask decider symbols)
        (directSourceCarrierCompactAtomWordPairs decider symbols).pairs⟩ :=
  rfl

theorem directSourceCarrierSelectedCompactAtomWordPairs_eq_nil_of_isEmpty
    [IsEmpty encoding.Γ] (symbols : List encoding.Γ) :
    directSourceCarrierSelectedCompactAtomWordPairs decider symbols =
      directSourceCarrierSelectedCompactAtomWordPairs decider [] := by
  cases symbols with
  | nil => rfl
  | cons symbol _ => exact isEmptyElim symbol

/-- Retained compact endpoint pairs in global key-major link order. -/
def directSourceCarrierRetainedCompactAtomWordPairs
    (symbols : List encoding.Γ) : DelimitedBinaryWordPairs.Input :=
  directSourceCarrierSelectedCompactAtomWordPairs decider symbols

theorem directSourceCarrierRetainedCompactAtomWordPairs_eq_selected
    (symbols : List encoding.Γ) :
    directSourceCarrierRetainedCompactAtomWordPairs decider symbols =
      directSourceCarrierSelectedCompactAtomWordPairs decider symbols :=
  rfl

end PeriodicCNFStripReduction
end LeanTrominoes

end
