/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableClauseNormalization
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataTargetTerminalGauge

/-! # Normalization of routed-variable target terminals -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Normalizing a translated target terminal adds its incidence-edge gauge,
so the resulting offset is exactly its lifted variable-site translate. -/
theorem externalWrappedVariableNormalization_targetTerminal_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (taggedIncidence : CNFIncidence Variable × Nat)
    (taggedMember :
      taggedIncidence ∈
        (PeriodicCNF.incidencesWithMetadata source).zipIdx)
    (translate : Cell) :
    let occurrence : CNFRouteOccurrence Variable :=
      ⟨taggedIncidence.1, taggedIncidence.2, translate⟩
    externalWrappedVariableNormalization source
        (.carrier (.terminal (occurrence.targetTerminal source))) =
      (⟨PeriodicPlanarSATVariable.terminal
          (occurrence.targetTerminal source).indexed .finish⟩,
        occurrence.variableOccurrence.2) := by
  let occurrence : CNFRouteOccurrence Variable :=
    ⟨taggedIncidence.1, taggedIncidence.2, translate⟩
  let baseOccurrence : CNFRouteOccurrence Variable :=
    ⟨taggedIncidence.1, taggedIncidence.2, (0, 0)⟩
  have edgeMember :=
    PeriodicCNF.tagged_incidence_edge_mem source taggedMember
  have gauge := retainedGauge_targetTerminal_eq_edgeOffset
    source wellFormed taggedIncidence.1 taggedIncidence.2 edgeMember
  change retainedDrawingWrappedPeriodicPlanarSATVariableGauge source
      ⟨PeriodicPlanarSATVariable.terminal
        (baseOccurrence.targetTerminal source).indexed .finish⟩ =
    taggedIncidence.1.edge.offset at gauge
  have indexedEq :
      (occurrence.targetTerminal source).indexed =
        (baseOccurrence.targetTerminal source).indexed := by
    rfl
  have endpointEq :
      (occurrence.targetTerminal source).endpoint = .finish := by
    rfl
  have translateEq :
      (occurrence.targetTerminal source).translate = translate := by
    rfl
  change externalWrappedVariableNormalization source
      (.carrier (.terminal (occurrence.targetTerminal source))) = _
  simp only [externalWrappedVariableNormalization,
    planarSATExternalVariableMap, normalizePlanarSATVariable]
  rw [indexedEq, endpointEq, translateEq, gauge]
  rw [CNFIncidence.edge_offset]
  simp [baseOccurrence, CNFRouteOccurrence.variableOccurrence,
    CNFRouteOccurrence.edge, Cell.add]

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
