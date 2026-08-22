/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedClauseSourceGauge

/-! # Endpoint normalization for routed source clauses -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Normalizing a routed source terminal retains its explicit neighboring
translation and introduces no additional canonical variable-gauge shift. -/
theorem externalWrappedVariableNormalization_sourceTerminal_eq
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
        (.carrier (.terminal (occurrence.sourceTerminal source))) =
      (⟨PeriodicPlanarSATVariable.terminal
          (occurrence.sourceTerminal source).indexed .start⟩,
        translate) := by
  let occurrence : CNFRouteOccurrence Variable :=
    ⟨taggedIncidence.1, taggedIncidence.2, translate⟩
  let baseOccurrence : CNFRouteOccurrence Variable :=
    ⟨taggedIncidence.1, taggedIncidence.2, (0, 0)⟩
  have edgeMember :=
    PeriodicCNF.tagged_incidence_edge_mem source taggedMember
  have gauge := retainedGauge_sourceTerminal_eq_zero
    source wellFormed taggedIncidence.1 taggedIncidence.2 edgeMember
  change retainedDrawingWrappedPeriodicPlanarSATVariableGauge source
      ⟨PeriodicPlanarSATVariable.terminal
        (baseOccurrence.sourceTerminal source).indexed .start⟩ =
    (0, 0) at gauge
  have occurrenceEq :
      occurrence = baseOccurrence.periodTranslate translate := by
    simp [occurrence, baseOccurrence,
      CNFRouteOccurrence.periodTranslate, Cell.add]
  have indexedEq :
      (occurrence.sourceTerminal source).indexed =
        (baseOccurrence.sourceTerminal source).indexed := by
    rw [occurrenceEq,
      CNFRouteOccurrence.sourceTerminal_periodTranslate]
    rfl
  have endpointEq :
      (occurrence.sourceTerminal source).endpoint = .start := by
    rfl
  have translateEq :
      (occurrence.sourceTerminal source).translate = translate := by
    rfl
  change externalWrappedVariableNormalization source
      (.carrier (.terminal (occurrence.sourceTerminal source))) = _
  simp only [externalWrappedVariableNormalization,
    planarSATExternalVariableMap,
    normalizePlanarSATVariable]
  rw [indexedEq, endpointEq, translateEq, gauge]
  simp [Cell.add]

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
