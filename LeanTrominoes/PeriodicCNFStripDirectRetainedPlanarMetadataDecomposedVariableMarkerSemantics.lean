/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataDecomposedVariableMarkerData
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataSegmentAtomMarkerSemantics

/-! # Exact counts of decomposed direct retained variable markers -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedDecomposedMarkerSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

noncomputable local instance directRetainedDecomposedMarkerSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The decomposed stream has exactly the terminal, atom, and crossing count
of the retained planar variable enumeration. -/
theorem directRetainedPlanarMetadataDecomposedVariableMarkers_eq_replicate_counts
    (symbols : List encoding.Γ) :
    directRetainedPlanarMetadataDecomposedVariableMarkers decider symbols =
      List.replicate
        (2 * FormulaShape.routedSegmentCount
              (directSourceFormulaShape decider symbols) +
          FormulaShape.variableCount
              (directSourceFormulaShape decider symbols) +
          13 * (orientedCrossings
            (directSourceFormula decider symbols).incidenceGraph).length)
        FormulaShapeDirectionOrdering.Token.variable := by
  unfold directRetainedPlanarMetadataDecomposedVariableMarkers
    directRetainedPlanarMetadataCrossingMarkers
  rw [directRetainedPlanarMetadataSegmentAtomMarkers_eq_replicate_shapeCounts,
    ← List.replicate_add]

end LeanTrominoes.PeriodicCNFStripReduction
