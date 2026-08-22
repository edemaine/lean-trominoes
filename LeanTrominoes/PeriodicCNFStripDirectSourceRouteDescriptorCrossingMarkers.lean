/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorGridSize
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataCrossingMarkerNumericPairData
import LeanTrominoes.PeriodicCNFStripDirectSourceNormalizedFormula
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaFacts
import LeanTrominoes.PeriodicThreeCNFExactSize
import LeanTrominoes.PeriodicThreeSATThreeExactSize

/-! # Direct crossing markers as a route-descriptor postprocess -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceDescriptorCrossingMarkersStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

noncomputable local instance directSourceDescriptorCrossingMarkersVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The guarded direct source always has at least one metadata incidence, so
its first descriptor carries the common drawing period. -/
theorem directSource_incidencesWithMetadata_ne_nil
    (symbols : List encoding.Γ) :
    incidencesWithMetadata (directSourceFormula decider symbols) ≠ [] := by
  intro empty
  have lengthZero := congrArg List.length empty
  rw [incidencesWithMetadata_length,
    directSourceFormula_eq_threeSATThree,
    PeriodicThreeSATThree.formula_presentationLiteralCount,
    PeriodicThreeCNF.formula_presentationLiteralCount_of_widthAtMostThree
      _ (formulaOfSymbols_widthAtMostThree decider symbols),
    formulaOfSymbols_presentationLiteralCount] at lengthZero
  simp only [List.length_nil] at lengthZero
  omega

/-- Thirteen finite markers per canonical descriptor crossing. -/
def directSourceRouteDescriptorCrossingMarkers
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  List.replicate
    (13 * routeDescriptorOrientedCrossingCount
      (numericRouteDescriptors (directSourceFormula decider symbols)))
    .variable

/-- The descriptor-only crossing postprocessor produces exactly the compact
numeric crossing-marker target used by retained planar metadata. -/
theorem directSourceRouteDescriptorCrossingMarkers_eq_numericPairMarkers
    (symbols : List encoding.Γ) :
    directSourceRouteDescriptorCrossingMarkers decider symbols =
      directRetainedPlanarMetadataCrossingNumericPairMarkers decider
        symbols := by
  unfold directSourceRouteDescriptorCrossingMarkers
    directRetainedPlanarMetadataCrossingNumericPairMarkers
  rw [PeriodicCNF.numericOrientedCrossingOccurrencePairs_length_eq_routeDescriptorCount
    (directSourceFormula decider symbols)
    (directSource_incidencesWithMetadata_ne_nil decider symbols)]

end PeriodicCNFStripReduction
end LeanTrominoes

end
