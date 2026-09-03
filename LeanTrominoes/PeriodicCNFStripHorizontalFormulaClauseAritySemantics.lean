/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalEncoderData
import LeanTrominoes.PeriodicCNFStripHorizontalFinalOrderingClauseAritySemantics

/-! # Clause arities of the final gauged horizontal formula -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

attribute [local instance] sourceVariableDecidableEq

/-- The final gauged horizontal formula emits the same polarity-normalized
arity sequence as the retained raw ordered Figure 9 endpoint. -/
theorem horizontalFormula_polarityClauseLengths_eq_raw
    (source : PeriodicCNF Nat) :
    (PeriodicOneInThreePolarityNormalization.formula
      (horizontalFormula source).erase).clauses.map List.length =
      (PeriodicOneInThreePolarityNormalization.formula
        (PeriodicOrthocrossing.retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          (sourceFormula source)).erase).clauses.map List.length := by
  simpa only [horizontalFormula] using
    PeriodicOrthocrossing.retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_polarityClauseLengths_eq_raw
      (sourceFormula source)
      (sourceFormula_isLocal source)
      (sourceFormula_widthAtMostThree source)
      (sourceFormula_occurrencesAtMostThree_canonicalBEq source)
      (sourceFormula_clausesNonempty source)

end LeanTrominoes.PeriodicCNFStripReduction
