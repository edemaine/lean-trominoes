/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFStripNativePlanarSemantics
import LeanTrominoes.PeriodicCNFStripHorizontalSemanticDrawingWitness
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationFreshGaugeLocality

/-! # Locality and the occurrence-three bound of the native planar candidate -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open PeriodicOneInThreePolarityNormalizationRouteSubdivision
attribute [local instance] sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq horizontalRibbonRoutedVariableDecidableEq
set_option maxHeartbeats 400000

theorem nativeRoutedFormula_local (source : PeriodicCNF Nat) :
    (horizontalRoutedFormulaComputed source).erase.IsLocal := by
  rw [horizontalRoutedFormulaComputed_eq_semanticData]
  apply formula_erase_isLocal
  · exact PeriodicOrthocrossing.retainedFinalGaugedFormula_isLocal (sourceFormula source)
      (sourceFormula_isLocal source) (sourceFormula_widthAtMostThree source)
      (sourceFormula_occurrencesAtMostThree_canonicalBEq source) (sourceFormula_clausesNonempty source)
  · intro clause member empty
    have arity := horizontalFormula_arityTwoOrThreeComputed source clause member
    simp [empty] at arity

theorem nativeRoutedFormula_occurrences (source : PeriodicCNF Nat) :
    (horizontalRoutedFormulaComputed source).erase.OccurrencesAtMost 3 := by
  rw [horizontalRoutedFormulaComputed_eq_semanticData]
  have bound := @CoordinatedAssemblyDrawingWitness.occurrences
    RoutedVariable horizontalRibbonRoutedVariableDecidableEq
    (horizontalSemanticRoutedFormula source) (horizontalSemanticRoutedPlacement source)
    (horizontalSemanticRoutedRibbonReadyPresentation source) (presentation source).drawing
    (horizontalSemanticDrawing_routingCertificate source)
  exact PeriodicCNF.occurrencesAtMost_congr_beq _ _ (by infer_instance) (by infer_instance) 3 _ bound

variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance nativePlanarLocalStackFintype (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

theorem nativePlanarInput_local (s : List encoding.Γ) : (nativePlanarInput decider s).1.IsLocal := by
  change ((nativeRoutedFormulaSource decider s).anchorNormalize.rename (nativeAtomRenaming decider s)).IsLocal
  rw [PeriodicCNF.local_rename]
  exact PeriodicCNF.anchorNormalize_local (nativeRoutedFormula_local _)

theorem nativePlanarInput_occurrences (s : List encoding.Γ) :
    (nativePlanarInput decider s).1.OccurrencesAtMost 3 := by
  change ((nativeRoutedFormulaSource decider s).anchorNormalize.rename (nativeAtomRenaming decider s)).OccurrencesAtMost 3
  rw [PeriodicCNF.occurrences_rename_iff _ (nativeAtomRenaming_injective decider s)]
  apply (nativeRoutedFormulaSource decider s).anchorNormalize_occurrencesAtMost 3
  exact PeriodicCNF.occurrencesAtMost_congr_beq _ _ (by infer_instance) (by infer_instance) 3 _
    (nativeRoutedFormula_occurrences _)

end LeanTrominoes.PeriodicCNFStripReduction
end
