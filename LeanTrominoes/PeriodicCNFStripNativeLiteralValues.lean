/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFStripNativeClauseArities
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationPresentationProperties

/-! # Native literal-value fields of the actual routed formula -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing PeriodicOneInThreePolarityNormalization
attribute [local instance] sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq horizontalRibbonRoutedVariableDecidableEq
set_option maxHeartbeats 800000

theorem nativeRoutedFormula_polarityNormalized (source : PeriodicCNF Nat) :
    FormulaPolarityNormalized (horizontalRoutedFormulaComputed source).erase := by
  rw [horizontalRoutedFormulaComputed_eq_semanticData]
  exact PeriodicOneInThreePolarityNormalizationRouteSubdivision.formula_polarityNormalized _ _ _

private def signFields (n : Nat) : List Nat :=
  (List.range n).map (fun i => (normalizedPolarity i).toNat)

private theorem signFields_formula {V : Type*} (formula : PeriodicCNF V)
    (normalized : FormulaPolarityNormalized formula) :
    (formula.clauses.map List.length).flatMap signFields =
      formula.clauses.flatMap (fun clause => clause.map (fun literal => literal.value.toNat)) := by
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro clause member
  have values := congrArg (List.map Bool.toNat) (normalized clause member)
  simpa only [List.map_map, Function.comp_def, signFields] using values.symm

variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance nativeValueStackFintype (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

noncomputable def nativeLiteralValuesCompiler :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun symbols => (horizontalRoutedFormulaComputed
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.clauses.flatMap
          (fun clause => clause.map (fun literal => literal.value.toNat))) := by
  let physical := TM2CompositionMachine.computableInPolyTime
    (directSourceFinalClauseDescriptorsComputableInPolyTime decider)
    (FiniteUnaryFieldBlockMap.computableInPolyTime (fun token =>
      (HorizontalRoutedRouteHeaderClauseFrame.tokenBlocks token).flatMap (fun block => signFields block.length)))
  apply TM2ComputableInPolyTime.of_eq physical
  intro symbols
  rw [← signFields_formula _ (nativeRoutedFormula_polarityNormalized _),
    ← nativeClauseArities_eq decider symbols]
  simp only [FiniteUnaryFieldBlockMap.values,
    HorizontalRoutedRouteHeaderClauseFrame.outputBlocks, List.flatMap_map, List.flatMap_assoc]

end LeanTrominoes.PeriodicCNFStripReduction
end
