/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataCrossingMarkerData

/-! # Exact semantics of quadratic pair-scan crossing markers -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedCrossingPairSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

noncomputable local instance directRetainedCrossingPairSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The pair scan emits exactly the original thirteen-per-oriented-crossing
marker word. -/
theorem directRetainedPlanarMetadataCrossingPairMarkers_eq_crossingMarkers
    (symbols : List encoding.Γ) :
    directRetainedPlanarMetadataCrossingPairMarkers decider symbols =
      directRetainedPlanarMetadataCrossingMarkers decider symbols := by
  unfold directRetainedPlanarMetadataCrossingPairMarkers
    directRetainedPlanarMetadataCrossingMarkers
  rw [orientedCrossingPairScan_length_eq_orientedCrossings]

end LeanTrominoes.PeriodicCNFStripReduction
