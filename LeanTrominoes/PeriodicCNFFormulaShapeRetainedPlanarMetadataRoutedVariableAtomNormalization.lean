/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableTargetNormalization
import LeanTrominoes.PeriodicCNFPlanarZeroVariableRouteSites

/-! # Normalization of routed-variable center atoms -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- A represented routed-variable center is a nonterminal canonical
prototype, so normalization preserves exactly its displayed site translate. -/
theorem externalWrappedVariableNormalization_atom_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (isLocal : source.incidenceGraph.IsLocal)
    (site : VariableRouteSite Variable)
    (siteMember : site ∈ drawingVariableRouteSites source) :
    externalWrappedVariableNormalization source (.atom site) =
      (⟨PeriodicPlanarSATVariable.atom site.1⟩, site.2) := by
  have zeroSiteMember :
      (site.1, (0, 0)) ∈ drawingVariableRouteSites source :=
    drawingVariableRouteSite_zero_mem source isLocal siteMember
  have valid :
      RetainedDrawingPeriodicPlanarSATVariableValid source
        (.atom site.1) :=
    zeroSiteMember
  have gauge :=
    retainedDrawingPeriodicPlanarSATVariableGauge_eq_zero_of_nonterminal
      source wellFormed (.atom site.1) valid (by
        intro indexed endpoint
        simp)
  have wrappedGauge :
      retainedDrawingWrappedPeriodicPlanarSATVariableGauge source
          ⟨PeriodicPlanarSATVariable.atom site.1⟩ =
        (0, 0) := by
    change
      (drawingPeriodicPlanarSATPlacement source).canonicalPositionGauge
          (.atom site.1) =
        (0, 0)
    exact gauge
  unfold externalWrappedVariableNormalization
  simp only [planarSATExternalVariableMap,
    normalizePlanarSATVariable, wrappedGauge]
  simp [Cell.add]

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
