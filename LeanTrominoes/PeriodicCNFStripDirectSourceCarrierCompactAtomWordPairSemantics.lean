/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierCompactAtomWordPairMaskSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCompactAtomWordSeparation

/-! # Semantics of retained direct-source compact carrier word pairs -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directCarrierCompactPairSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directCarrierCompactPairSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The direct retained compact word pairs are exactly the normalized
semantic retained carrier-link endpoint pairs, in presentation order. -/
theorem directSourceCarrierRetainedCompactAtomWordPairs_eq_normalizedLinks
    (symbols : List encoding.Γ) :
    (directSourceCarrierRetainedCompactAtomWordPairs
      decider symbols).pairs =
      let source := directSourceFormula decider symbols
      ((retainedDrawingCompleteCarrierLinks source.incidenceGraph).map
        (PeriodicEquality.normalizeLink
          (carrierWrappedVariableNormalization source))).map fun link =>
            (directSourceFinalCompactAtomWord source link.first,
              directSourceFinalCompactAtomWord source link.second) := by
  let source := directSourceFormula decider symbols
  have inputEq :=
    (directSourceCarrierRetainedCompactAtomWordPairs_eq_maskTarget
      decider symbols).trans
      (directSourceCarrierCompactAtomWordPairMaskTarget_eq_normalizedWords
        decider
        (DirectSourceFinalIndexedAtomWords.sourceVariableWord source)
        symbols)
  have pairsEq := congrArg DelimitedBinaryWordPairs.Input.pairs inputEq
  simpa [source, directSourceCarrierNormalizedCompactAtomWordPairs,
    directSourceFinalCompactAtomWord] using pairsEq

end PeriodicCNFStripReduction
end LeanTrominoes

end
