/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataDirectionDescriptorBlockData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataVariableEnumeration

/-! # Canonical direct retained metadata variable markers -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedVariableMarkersStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directRetainedVariableMarkersDecidableEq :
    DecidableEq Variable := Classical.decEq _

/-- On direct PSPACE source symbols, the abstract distinct-variable marker
suffix is exactly one marker per canonical retained periodic variable. -/
theorem directRetainedPlanarMetadataVariableMarkers_eq_retainedVariables
    (symbols : List encoding.Γ) :
    directRetainedPlanarMetadataVariableMarkers decider symbols =
      List.replicate
        (retainedDrawingPeriodicPlanarSATVariables
          (sourceFormula
            (PolySpaceCompiler.formulaOfSymbols decider symbols))).length
        .variable := by
  unfold directRetainedPlanarMetadataVariableMarkers
  apply
    FormulaShapeRetainedPlanarMetadataDirection.variableMarkers_eq_replicate_retainedVariables
  · exact sourceFormula_occurrencesAtMostThree_canonicalBEq _
  · exact PeriodicCNF.incidenceGraph_isWellFormed _
  · exact PeriodicCNF.incidenceGraph_degreeAtMost
      (sourceFormula_widthAtMostThree _)
      (sourceFormula_occurrencesAtMostThree_canonicalBEq _)
  · exact PeriodicCNF.incidenceGraph_isLocal
      (sourceFormula_isLocal _)

end LeanTrominoes.PeriodicCNFStripReduction
