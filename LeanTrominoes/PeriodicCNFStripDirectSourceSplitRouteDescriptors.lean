/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceNormalizedFormula
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaForwardLocal
import LeanTrominoes.PeriodicCNFStripDirectThreeCNFSourceZeroAnchors
import LeanTrominoes.PeriodicThreeSATThreeNormalizedRoutedVariablePairScan
import LeanTrominoes.PeriodicThreeSATThreeSplitRouteDescriptorEnumerationSemantics

/-! # Explicit route descriptors for direct strip sources -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceSplitRouteDescriptorsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

private noncomputable def
    directSourceSplitRouteDescriptorsStructuralVariableDecidableEq :
    DecidableEq Variable :=
  inferInstance

noncomputable local instance directSourceSplitRouteDescriptorsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The semantic numeric route stream of a direct source is the explicit
copied-incidence prefix followed by the two cycle incidences per occurrence. -/
theorem directSource_numericRouteDescriptors_eq_splitRouteDescriptors
    (symbols : List encoding.Γ) :
    numericRouteDescriptors (directSourceFormula decider symbols) =
      PeriodicThreeSATThree.splitRouteDescriptors
        (PeriodicThreeCNF.formula
          (PolySpaceCompiler.formulaOfSymbols decider symbols)) := by
  rw [directSourceFormula_eq_threeSATThree]
  have instanceEq :
      directSourceSplitRouteDescriptorsVariableDecidableEq =
        directSourceSplitRouteDescriptorsStructuralVariableDecidableEq :=
    Subsingleton.elim _ _
  rw [instanceEq]
  exact @PeriodicThreeSATThree.numericRouteDescriptors_formula_eq_splitRouteDescriptors
    (ThreeCNFVariable Nat) inferInstance
    directSourceSplitRouteDescriptorsStructuralVariableDecidableEq _

/-- Replace the direct source's named equality implementation in the split
descriptor stream by the structural implementation used by generic
occurrence-splitting theorems. -/
theorem directSource_splitRouteDescriptors_eq_structural
    (symbols : List encoding.Γ) :
    PeriodicThreeSATThree.splitRouteDescriptors
        (PeriodicThreeCNF.formula
          (PolySpaceCompiler.formulaOfSymbols decider symbols)) =
      @PeriodicThreeSATThree.splitRouteDescriptors
        (ThreeCNFVariable Nat) inferInstance
        directSourceSplitRouteDescriptorsStructuralVariableDecidableEq
        (PeriodicThreeCNF.formula
          (PolySpaceCompiler.formulaOfSymbols decider symbols)) := by
  have instanceEq :
      directSourceSplitRouteDescriptorsVariableDecidableEq =
        directSourceSplitRouteDescriptorsStructuralVariableDecidableEq :=
    Subsingleton.elim _ _
  rw [instanceEq]

/-- The direct split descriptor square retains one normalized complete
routed-variable site per literal occurrence of the width-three source. -/
theorem directSource_normalizedRoutedVariablePairDescriptorScan_eq_fullSites
    (symbols : List encoding.Γ) :
    normalizedRoutedVariablePairDescriptorScan
        (PeriodicThreeSATThree.splitRouteDescriptors
          (PeriodicThreeCNF.formula
            (PolySpaceCompiler.formulaOfSymbols decider symbols))) =
      (List.range (PeriodicCNF.presentationLiteralCount
          (PeriodicThreeCNF.formula
            (PolySpaceCompiler.formulaOfSymbols decider symbols)))).flatMap
        (fun _targetIndex => routedVariableFullSiteBlock) := by
  have instanceEq :
      directSourceSplitRouteDescriptorsVariableDecidableEq =
        directSourceSplitRouteDescriptorsStructuralVariableDecidableEq :=
    Subsingleton.elim _ _
  rw [instanceEq]
  exact
    PeriodicThreeSATThree.normalizedRoutedVariablePairDescriptorScan_splitRouteDescriptors
      (PeriodicThreeCNF.formula
        (PolySpaceCompiler.formulaOfSymbols decider symbols))
      (PeriodicThreeCNF.formula_isForwardLocal
        (formulaOfSymbols_isForwardLocal decider symbols))
      (directThreeCNFSource_zeroAnchored decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction
