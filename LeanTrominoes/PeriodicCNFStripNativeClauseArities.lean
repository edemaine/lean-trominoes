/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalParentIndexHorizontalSemantics
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedFormulaSemanticBridge
import LeanTrominoes.FiniteUnaryFieldBlockMapCompiler

/-! # Compiling actual clause lengths in the native routed formula -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing
attribute [local instance] sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq horizontalRibbonRoutedVariableDecidableEq
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance nativeArityStackFintype (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack
set_option maxHeartbeats 800000

private theorem normalizedClauseLengths (source : PeriodicCNF Nat) :
    (horizontalSemanticNormalizedRibbonSource source).erase.clauses.map List.length =
      (horizontalRoutedFormulaComputed source).erase.clauses.map List.length := by
  rw [horizontalRoutedFormulaComputed_eq_semanticData]
  simp [horizontalSemanticNormalizedRibbonSource,
    PeriodicPlanarOneInThreeToThreeDM.normalizedPositionedSource,
    PositionedPeriodicCNF.erase_anchorNormalize, PositionedPeriodicCNF.erase_scale,
    PeriodicCNF.anchorNormalize, List.map_map, Function.comp_def]

theorem nativeClauseArities_eq (symbols : List encoding.Γ) :
    (HorizontalRoutedRouteHeaderClauseFrame.outputBlocks
      (directSourceFinalClauseDescriptors decider symbols)).map List.length =
    (horizontalRoutedFormulaComputed
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.clauses.map List.length := by
  rw [directSourceFinalClauseFrameBlockLengths_eq_horizontal, normalizedClauseLengths]

noncomputable def nativeClauseAritiesCompiler :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun symbols => (horizontalRoutedFormulaComputed
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.clauses.map List.length) := by
  let physical := TM2CompositionMachine.computableInPolyTime
    (directSourceFinalClauseDescriptorsComputableInPolyTime decider)
    (FiniteUnaryFieldBlockMap.computableInPolyTime (fun token =>
      (HorizontalRoutedRouteHeaderClauseFrame.tokenBlocks token).map List.length))
  apply TM2ComputableInPolyTime.of_eq physical
  intro symbols
  rw [← nativeClauseArities_eq decider symbols]
  simp only [FiniteUnaryFieldBlockMap.values,
    HorizontalRoutedRouteHeaderClauseFrame.outputBlocks, List.map_flatMap]

end LeanTrominoes.PeriodicCNFStripReduction
end
