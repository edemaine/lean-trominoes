/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorLocalShape
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCompactOccurrenceAtomWordFamilies
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaForwardLocalNamed
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorPairFieldTagSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceRoutedVariableCompactAtomWordData
import LeanTrominoes.PeriodicCNFStripDirectSourceSplitRouteDescriptors
import LeanTrominoes.PeriodicCNFStripDirectThreeCNFOccurrencePositiveOffsets
import LeanTrominoes.PeriodicOrthocrossingRoutedVariableCompactAtomWordStreamSemantics
import LeanTrominoes.PeriodicThreeSATThreeRoutedVariableCompactAtomWordFinalBlock

/-! # Direct-source routed-variable compact atom-word semantics -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRoutedVariableCompactSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directRoutedVariableCompactSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The physical direct stream encodes exactly the semantic descriptor-pair
scan. -/
theorem directSourceRoutedVariableCompactAtomWordTokens_eq_encode
    (symbols : List encoding.Γ) :
    directSourceRoutedVariableCompactAtomWordTokens decider symbols =
      DelimitedBinaryWords.encode
        (directSourceRoutedVariableCompactAtomWords decider symbols) := by
  unfold directSourceRoutedVariableCompactAtomWordTokens
  rw [directSourceRouteDescriptorPairFieldTags_eq]
  rw [RoutedVariableCompactAtomWordStream.emittedStream_encodeDescriptorPairs_eq_pairBlocks]
  · rfl
  · intro pair pairMember
    exact PeriodicCNF.numericRouteDescriptors_all_hasLocalShape
      (directSourceFormula decider symbols)
      (directSourceFormula_isForwardLocal decider symbols)
      pair.2 (List.mem_product.mp pairMember).2

/-- The exact final-formula routed-variable compact atom-word block. -/
def directSourceFinalRoutedVariableCompactAtomWords
    (symbols : List encoding.Γ) : DelimitedBinaryWords.Input :=
  ⟨directSourceFinalCompactRoutedVariableAtomWordBlock decider symbols⟩

/-- The compiled descriptor-pair scan is exactly the repeated endpoint-word
block used by the final five-family occurrence presentation. -/
theorem directSourceRoutedVariableCompactAtomWords_eq_final
    (symbols : List encoding.Γ) :
    directSourceRoutedVariableCompactAtomWords decider symbols =
      directSourceFinalRoutedVariableCompactAtomWords decider symbols := by
  let source := PeriodicThreeCNF.formula
    (PolySpaceCompiler.formulaOfSymbols decider symbols)
  have sourceLocal : source.IsLocal := by
    apply PeriodicThreeCNF.formula_isLocal
    exact (formulaOfSymbols_sourceAdmissible decider symbols).2.1
  have positiveOffsets :
      ∀ incidence ∈ PeriodicThreeSATThree.occurrenceIncidences source,
        incidence.edge.offset = (0, 0) ∨
          incidence.edge.offset = (1, 0) := by
    simpa only [source] using
      directThreeCNFSource_occurrenceIncidences_positiveOffsets
        decider symbols
  unfold directSourceRoutedVariableCompactAtomWords
    directSourceFinalRoutedVariableCompactAtomWords
    directSourceFinalCompactRoutedVariableAtomWordBlock
    directThreeCNFSourceFormula
  rw [directSource_numericRouteDescriptors_eq_splitRouteDescriptors]
  rw [directSource_splitRouteDescriptors_eq_structural]
  exact congrArg DelimitedBinaryWords.Input.mk
    (PeriodicThreeSATThree.routedVariableCompactAtomWordPairScan_split_eq_canonicalLinks
      source sourceLocal positiveOffsets)

end PeriodicCNFStripReduction
end LeanTrominoes

end
