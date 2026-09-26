/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFStripNativePlanarEncoding
import LeanTrominoes.PeriodicCNFStripHorizontalFormula
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationFreshGaugeOneDimensional
import LeanTrominoes.PeriodicPlanarSATInjectiveRenaming
import LeanTrominoes.PositionedPeriodicCNFAnchorNormalizationDrawing

/-! # Logical and geometric semantics of the fully encoded planar candidate -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open PositionedPeriodicCNF PeriodicOneInThreePolarityNormalizationRouteSubdivision
attribute [local instance] sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq horizontalRibbonRoutedVariableDecidableEq
set_option maxHeartbeats 400000

private theorem drawing_classical {V : Type} [DecidableEq V]
    (source : PositionedPeriodicCNF V) (placement : PeriodicVariablePlacement V) (routes : IncidenceRoutes) :
    incidenceDrawing source placement routes = @incidenceDrawing V (Classical.decEq V) source placement routes := by
  exact congrArg (fun d => @incidenceDrawing V d source placement routes) (Subsingleton.elim _ _)

private theorem graph_classical {V : Type} [DecidableEq V] (source : PeriodicCNF V) :
    source.incidenceGraph = @PeriodicCNF.incidenceGraph V (Classical.decEq V) source := by
  exact congrArg (fun d => @PeriodicCNF.incidenceGraph V d source) (Subsingleton.elim _ _)

private theorem compatible_classical {V : Type} [Primcodable V] [DecidableEq V]
    (graph : PeriodicGraph V) (drawing : PeriodicGridDrawing) :
    PeriodicGridDrawing.FiniteCertificate.Compatible graph drawing ↔
      @PeriodicGridDrawing.FiniteCertificate.Compatible V (Classical.decEq V) graph drawing := by
  exact iff_of_eq (congrArg (fun d => @PeriodicGridDrawing.FiniteCertificate.Compatible V d graph drawing)
    (Subsingleton.elim _ _))

private theorem compatible_extract {V : Type} [Primcodable V] [DecidableEq V]
    (graph : PeriodicGraph V) (drawing : PeriodicGridDrawing) (h : drawing.IsCompatible graph) :
    PeriodicGridDrawing.FiniteCertificate.Compatible graph drawing := h.2

private theorem horizontalFormula_correct (source : PeriodicCNF Nat) :
    PeriodicOneInThree.Satisfiable (horizontalFormula source).erase ↔
      PeriodicCNF.LocalPeriodicCNF1DSAT source := by
  exact (PeriodicOrthocrossing.retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_satisfiable_iff
    (sourceFormula source) (sourceFormula_isLocal source) (sourceFormula_widthAtMostThree source)
    (sourceFormula_occurrencesAtMostThree_canonicalBEq source) (sourceFormula_clausesNonempty source)).trans
    ((PeriodicOrthocrossing.retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_satisfiable_iff
      (sourceFormula source) (sourceFormula_isLocal source) (sourceFormula_widthAtMostThree source)
      (sourceFormula_occurrencesAtMostThree_canonicalBEq source)).trans (sourceFormula_correct source).symm)

theorem nativeRoutedFormula_correct (source : PeriodicCNF Nat) :
    PeriodicOneInThree.Satisfiable (horizontalRoutedFormulaComputed source).erase ↔
      PeriodicCNF.LocalPeriodicCNF1DSAT source := by
  rw [horizontalRoutedFormulaComputed_eq_semanticData]
  exact (satisfiable_iff (horizontalFormula source) (horizontalPlacement source) (horizontalRoutes source)).trans
    (horizontalFormula_correct source)

theorem nativeRoutedFormula_oneDimensional (source : PeriodicCNF Nat) :
    (horizontalRoutedFormulaComputed source).erase.IsOneDimensional := by
  rw [horizontalRoutedFormulaComputed_eq_semanticData]
  exact formula_erase_isOneDimensional _ _ (horizontalFormula_isOneDimensional source)

theorem nativeRoutedDrawing_continuous (source : PeriodicCNF Nat) :
    (incidenceDrawing (horizontalRoutedFormulaComputed source)
      (horizontalRoutedPlacementComputed source) (horizontalRoutedRoutesComputed source)).IsContinuouslyPlanar := by
  rw [horizontalRoutedFormulaComputed_eq_semanticData, horizontalRoutedPlacementComputed_eq_semanticData,
    horizontalRoutedRoutesComputed_eq_semanticData]
  exact incidenceDrawing_isContinuouslyPlanar
    (horizontalSemanticFinalGaugedPresentation source).toContinuousPlanarIncidencePresentation

theorem nativeRoutedDrawing_finiteCompatible (source : PeriodicCNF Nat) :
    PeriodicGridDrawing.FiniteCertificate.Compatible (horizontalRoutedFormulaComputed source).erase.incidenceGraph
      (incidenceDrawing (horizontalRoutedFormulaComputed source)
        (horizontalRoutedPlacementComputed source) (horizontalRoutedRoutesComputed source)) := by
  have compatible := compatible_extract _ _ (nativeRoutedPresentation source).compatible
  simpa only [nativeRoutedPresentation_routes, compatible_classical, drawing_classical, graph_classical] using compatible

variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance nativePlanarSemanticsStackFintype (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

theorem nativePlanarInput_exactOne (s : List encoding.Γ) :
    PeriodicOneInThree.Satisfiable (nativePlanarInput decider s).1 ↔
      PeriodicCNF.LocalPeriodicCNF1DSAT (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s) :=
  (nativeNormalizedFormula_exactOne decider s).trans (nativeRoutedFormula_correct _)

theorem nativePlanarInput_oneDimensional (s : List encoding.Γ) :
    (nativePlanarInput decider s).1.IsOneDimensional := by
  change ((nativeRoutedFormulaSource decider s).anchorNormalize.rename (nativeAtomRenaming decider s)).IsOneDimensional
  rw [PeriodicCNF.oneDimensional_rename]
  exact PeriodicCNF.anchorNormalize_isOneDimensional (nativeRoutedFormula_oneDimensional _)

theorem nativePlanarInput_width (s : List encoding.Γ) : (nativePlanarInput decider s).1.WidthAtMost 3 := by
  change ((nativeRoutedFormulaSource decider s).anchorNormalize.rename (nativeAtomRenaming decider s)).WidthAtMost 3
  rw [PeriodicCNF.width_rename]
  apply PeriodicCNF.anchorNormalize_widthAtMost
  intro clause member
  have arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree (nativeRoutedFormulaSource decider s) := by
    rw [nativeRoutedFormulaSource, horizontalRoutedFormulaComputed_eq_semanticData]
    exact horizontalSemanticRoutedFormula_arityTwoOrThreeComputed _
  have := arity clause member
  change clause.length ≤ 3
  omega

theorem nativePlanarInput_planar (s : List encoding.Γ) : (nativePlanarInput decider s).2.IsContinuouslyPlanar := by
  simpa only [nativePlanarInput, nativeRoutedDrawing, drawing_classical] using
    nativeRoutedDrawing_continuous (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s)

theorem nativePlanarInput_compatible (s : List encoding.Γ) :
    PeriodicGridDrawing.FiniteCertificate.Compatible
      (nativePlanarInput decider s).1.incidenceGraph (nativePlanarInput decider s).2 := by
  change PeriodicGridDrawing.FiniteCertificate.Compatible
    (((nativeRoutedFormulaSource decider s).anchorNormalize.rename (nativeAtomRenaming decider s)).incidenceGraph)
    (nativeRoutedDrawing decider s)
  rw [PeriodicCNF.finiteCompatible_rename _ (nativeAtomRenaming_injective decider s),
    PeriodicCNF.incidenceGraph_anchorNormalize]
  simpa only [nativeRoutedFormulaSource, nativeRoutedDrawing, compatible_classical, drawing_classical, graph_classical] using
    nativeRoutedDrawing_finiteCompatible (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s)

end LeanTrominoes.PeriodicCNFStripReduction
end
