/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalExactMetadataPolarityOperationSemantics
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedFormulaBridge
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationSourceIndexedAtoms

/-! # Actual horizontal atoms decoded from the direct polarity schedule -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicOneInThreePolarityNormalizationRouteSubdivision

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance sourceIndexedAtomsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance sourceIndexedAtomsVariableDecidableEq : DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The direct schedule selects precisely the actual original or fresh atom
at every horizontal output incidence, in the same order as its route words. -/
theorem directFigureNinePolarityRoutePairs_sourceIndexedAtoms_eq_horizontal
    (symbols : List encoding.Γ) :
    (List.zipWith
      (fun sourceClauseIndex pair =>
        sourceIndexedDescriptorOf sourceClauseIndex pair.1.polarity.indexed)
      (directFigureNinePolarityRoutePairSourceClauseIndices decider symbols)
      (directFigureNinePolarityRoutePairs decider symbols)).map
        (fun descriptor => descriptor.atom?
          (refinedSource (directSourceFinalGaugedFormula decider symbols)
            (directSourceFinalGaugedPlacement decider symbols)).erase) =
      (horizontalRoutedFormulaComputed
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.clauses.flatMap
          (fun clause => clause.map (fun literal => some literal.atom)) := by
  have positionedEq :
      formula (directSourceFinalGaugedFormula decider symbols)
        (directSourceFinalGaugedPlacement decider symbols)
        (directSourceFinalGaugedIncidenceRoutes decider symbols) =
      horizontalRoutedFormulaComputed
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols) := by
    rw [horizontalRoutedFormulaComputed_eq_semantic]
    unfold directSourceFinalGaugedFormula directSourceFinalClockwiseFormula
      directSourceFinalGaugedPlacement directSourceFinalGaugedIncidenceRoutes
      directSourceFormula
    rfl
  rw [directFigureNinePolarityRoutePairs_sourceIndexedDescriptor_eq_exactMetadata,
    List.map_map, ← positionedEq]
  simp only [Function.comp_def, directSourceFinalExactMetadataRouteBlocks]
  exact exactMetadataRouteBlocks_map_atom?
    (directSourceFinalGaugedFormula decider symbols)
    (directSourceFinalGaugedPlacement decider symbols)
    (directSourceFinalGaugedIncidenceRoutes decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction

end
