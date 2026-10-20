/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Planar.PeriodicPlanarSATGeometricEndpoints
import LeanTrominoes.SAT.Planar.PeriodicPlanarOrdinaryLinePolySpaceCompleteness
import LeanTrominoes.SAT.Planar.PeriodicPlanarExactOneLinePolySpaceCompleteness
import LeanTrominoes.SAT.ExactOne.PeriodicOneInThreePolarityNormalizationEndpointContacts

/-! # Polynomial-time hardness maps retain the full supplied geometry -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open PeriodicPlanarSAT PositionedPeriodicCNF PeriodicOneInThreePolarityNormalizationRouteSubdivision
attribute [local instance] sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq horizontalRibbonRoutedVariableDecidableEq
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 2048

private theorem drawing_classical {V : Type} [DecidableEq V]
    (source : PositionedPeriodicCNF V) (placement : PeriodicVariablePlacement V) (routes : IncidenceRoutes) :
    incidenceDrawing source placement routes=@incidenceDrawing V (Classical.decEq V) source placement routes := by
  exact congrArg (fun d => @incidenceDrawing V d source placement routes) (Subsingleton.elim _ _)

 theorem nativeRoutedDrawing_strongGeometry (source : PeriodicCNF Nat) :
    StrongGeometry (incidenceDrawing (horizontalRoutedFormulaComputed source)
      (horizontalRoutedPlacementComputed source) (horizontalRoutedRoutesComputed source)) := by
  constructor
  · have orthogonal := (nativeRoutedPresentation source).orthogonal
    simpa only [nativeRoutedPresentation_routes] using orthogonal
  · rw [horizontalRoutedFormulaComputed_eq_semanticData,horizontalRoutedPlacementComputed_eq_semanticData,
      horizontalRoutedRoutesComputed_eq_semanticData]
    exact incidenceDrawing_isRibbonReady
      (horizontalSemanticFinalGaugedPresentation source).toHaloBoundedRibbonReadyIncidencePresentation
      (horizontalSemanticFinalGaugedPresentation source).unitSteps

variable {Input : Type} {encoding : _root_.LeanTrominoes.FiniteEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance geometricHardnessStackFintype (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

 theorem nativePlanarInput_strongGeometry (s : List encoding.Γ) :
    StrongGeometry (nativePlanarInput decider s).2 := by
  simpa only [nativePlanarInput,nativeRoutedDrawing,drawing_classical] using
    nativeRoutedDrawing_strongGeometry (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s)

 theorem directSource_strongGeometry
    (source : PeriodicCNF.ProgramSource encoding language) (s : List encoding.Γ) :
    StrongGeometry (ThreeOccurrenceGeometry.drawing (directSourceFormula source s)) := by
  apply ThreeOccurrenceGeometry.strongGeometry
  · exact sourceFormula_isLocal (source.formulaOfSymbols s)
  · exact sourceFormula_widthAtMostThree (source.formulaOfSymbols s)
  · exact PeriodicCNF.occurrencesAtMost_congr_beq _ _ (by infer_instance) (by infer_instance) 3 _
      (sourceFormula_occurrencesAtMostThree_canonicalBEq (source.formulaOfSymbols s))
  · exact sourceFormula_clausesNonempty (source.formulaOfSymbols s)

 theorem nativeOrdinaryInput_strongGeometry (s : List encoding.Γ) :
    StrongGeometry (nativeOrdinaryInput decider s).2 := by
  change StrongGeometry (ThreeOccurrenceGeometry.drawing
    (directSourceFormula (PeriodicCNF.ProgramSource.ofDecider decider) s))
  exact directSource_strongGeometry (PeriodicCNF.ProgramSource.ofDecider decider) s


end LeanTrominoes.PeriodicCNFStripReduction
namespace LeanTrominoes.PeriodicPlanarSAT

 theorem geometricOrdinary_PSPACEHard : Complexity.PSPACEHard FlatEncoding.finEncoding
    (Geometric Orbit.LocalOneDimensionalProblem) := by
  intro A encoding language membership
  obtain ⟨decider⟩ := membership
  refine ⟨PeriodicCNFStripReduction.nativeOrdinaryReduction decider,?_,?_⟩
  · exact ⟨Complexity.FiniteAlphabetComputableInPolyTime.ofComputableInPolyTime
      (PeriodicCNFStripReduction.nativeOrdinaryReductionCompiler decider)⟩
  · intro input
    exact (PeriodicCNFStripReduction.nativeOrdinaryReduction_correct decider input).trans
      (and_iff_left (PeriodicCNFStripReduction.nativeOrdinaryInput_strongGeometry decider (encoding.encode input))).symm

 theorem geometricOrdinaryThree_PSPACEHard : Complexity.PSPACEHard FlatEncoding.finEncoding
    (Geometric Orbit.LocalOneDimensionalThreeOccurrenceProblem) := by
  intro A encoding language membership
  obtain ⟨decider⟩ := membership
  refine ⟨PeriodicCNFStripReduction.nativeOrdinaryReduction decider,?_,?_⟩
  · exact ⟨Complexity.FiniteAlphabetComputableInPolyTime.ofComputableInPolyTime
      (PeriodicCNFStripReduction.nativeOrdinaryReductionCompiler decider)⟩
  · intro input
    exact (PeriodicCNFStripReduction.nativeOrdinaryReduction_three_correct decider input).trans
      (and_iff_left (PeriodicCNFStripReduction.nativeOrdinaryInput_strongGeometry decider (encoding.encode input))).symm

 theorem geometricExactOne_PSPACEHard : Complexity.PSPACEHard FlatEncoding.finEncoding
    (Geometric Unbounded.LocalOneDimensionalExactOneProblem) := by
  intro A encoding language membership
  obtain ⟨decider⟩ := membership
  refine ⟨PeriodicCNFStripReduction.nativePlanarReduction decider,?_,?_⟩
  · exact ⟨Complexity.FiniteAlphabetComputableInPolyTime.ofComputableInPolyTime
      (PeriodicCNFStripReduction.nativePlanarReductionCompiler decider)⟩
  · intro input
    exact (PeriodicCNFStripReduction.nativePlanarReduction_correct decider input).trans
      (and_iff_left (PeriodicCNFStripReduction.nativePlanarInput_strongGeometry decider (encoding.encode input))).symm

 theorem geometricExactOneThree_PSPACEHard : Complexity.PSPACEHard FlatEncoding.finEncoding
    (Geometric Unbounded.LocalOneDimensionalExactOneThreeOccurrenceProblem) := by
  intro A encoding language membership
  obtain ⟨decider⟩ := membership
  refine ⟨PeriodicCNFStripReduction.nativePlanarReduction decider,?_,?_⟩
  · exact ⟨Complexity.FiniteAlphabetComputableInPolyTime.ofComputableInPolyTime
      (PeriodicCNFStripReduction.nativePlanarReductionCompiler decider)⟩
  · intro input
    exact (PeriodicCNFStripReduction.nativePlanarReduction_three_correct decider input).trans
      (and_iff_left (PeriodicCNFStripReduction.nativePlanarInput_strongGeometry decider (encoding.encode input))).symm

end LeanTrominoes.PeriodicPlanarSAT
