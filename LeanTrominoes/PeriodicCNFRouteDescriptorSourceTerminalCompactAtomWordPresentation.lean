/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceMetadataClausePartition
import LeanTrominoes.PeriodicCNFRouteDescriptorSourceTerminalCompactAtomWordSemantics

/-! # Presentation order of source-terminal compact words -/

namespace LeanTrominoes
namespace PeriodicCNF

open PeriodicOrthocrossing
open FormulaShapeRetainedPlanarMetadataDirection

/-- Descriptor-order source-terminal words are exactly the clause-major,
literal-minor routed-clause terminal words. -/
theorem numericRouteDescriptors_sourceTerminalCompactWords_eq
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (sourceWord : Variable → List Bool) :
    (RouteDescriptorSourceTerminalCompactWords.words
      (numericRouteDescriptors formula)).words =
      formula.clauses.zipIdx.flatMap fun taggedClause =>
        (clauseRouteOccurrencesAt formula
          (taggedClause.2, (0, 0))).map fun occurrence =>
            RetainedCompactAtomWords.word sourceWord
              (externalWrappedVariableNormalization formula
                (.carrier (.terminal
                  (occurrence.sourceTerminal formula)))).1 := by
  unfold RouteDescriptorSourceTerminalCompactWords.words
    numericRouteDescriptors
  rw [List.map_map]
  rw [← clauses_flatMap_filter_incidencesWithMetadata_zipIdx formula]
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro taggedClause _taggedClauseMember
  unfold clauseRouteOccurrencesAt
  rw [List.map_map]
  apply List.map_congr_left
  intro taggedIncidence taggedIncidenceMember
  have taggedMember :
      taggedIncidence ∈ formula.incidencesWithMetadata.zipIdx :=
    List.mem_of_mem_filter taggedIncidenceMember
  exact numericRouteDescriptor_sourceTerminalCompactWord
    formula wellFormed sourceWord taggedIncidence taggedMember

end PeriodicCNF
end LeanTrominoes
