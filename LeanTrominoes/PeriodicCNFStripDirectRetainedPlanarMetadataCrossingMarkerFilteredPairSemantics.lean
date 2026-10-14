/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataCrossingMarkerPairSemantics

/-! # Exact semantics of filtered crossing-pair markers -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


noncomputable local instance directRetainedCrossingFilteredPairSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Removing the redundant dedup pass preserves the crossing-marker word. -/
theorem directRetainedPlanarMetadataCrossingFilteredPairMarkers_eq_pairMarkers
    (symbols : List encoding.Γ) :
    directRetainedPlanarMetadataCrossingFilteredPairMarkers decider symbols =
      directRetainedPlanarMetadataCrossingPairMarkers decider symbols := by
  unfold directRetainedPlanarMetadataCrossingFilteredPairMarkers
    directRetainedPlanarMetadataCrossingPairMarkers
  rw [orientedCrossingPairScan_eq_filters]

end LeanTrominoes.PeriodicCNFStripReduction
