/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierVariableNormalizationData
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierCompactAtomWordPairData
import LeanTrominoes.PeriodicOrthocrossingRetainedCompactAtomWord

/-! # Semantic target for direct compact carrier word pairs -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directCarrierCompactPairSemanticDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directCarrierCompactPairSemanticDataVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Compact endpoint-word pairs of the wrapped normalized semantic retained
carrier links. -/
def directSourceCarrierNormalizedCompactAtomWordPairs
    (sourceWord : Variable → List Bool)
    (symbols : List encoding.Γ) : DelimitedBinaryWordPairs.Input :=
  let source := directSourceFormula decider symbols
  ⟨((retainedDrawingCompleteCarrierLinks source.incidenceGraph).map
    (PeriodicEquality.normalizeLink
      (carrierWrappedVariableNormalization source))).map fun link =>
        (RetainedCompactAtomWords.word sourceWord link.first,
          RetainedCompactAtomWords.word sourceWord link.second)⟩

end PeriodicCNFStripReduction
end LeanTrominoes

end
