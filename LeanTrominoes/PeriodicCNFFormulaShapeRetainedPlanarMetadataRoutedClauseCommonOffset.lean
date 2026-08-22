/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedClauseEndpointNormalization

/-! # Common periodic offsets in routed source clauses -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Before clause anchoring, every literal of one routed source clause has
exactly the clause site's common neighboring translation. -/
theorem periodicizeRoutedClauseAt_external_eq_commonOffset
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (site : ClauseRouteSite) :
    PeriodicEquality.periodicizeClause
        (externalWrappedVariableNormalization source)
        (routedClauseAt source site) =
      (clauseRouteOccurrencesAt source site).map fun occurrence =>
        (⟨⟨PeriodicPlanarSATVariable.terminal
            (occurrence.sourceTerminal source).indexed .start⟩,
          site.2, occurrence.incidence.literal.value⟩ :
          PeriodicLiteral
            (WrappedPeriodicPlanarSATVariable Variable)) := by
  unfold PeriodicEquality.periodicizeClause routedClauseAt
  rw [List.map_map]
  apply List.map_congr_left
  intro occurrence occurrenceMember
  rw [clauseRouteOccurrencesAt] at occurrenceMember
  rcases List.mem_map.mp occurrenceMember with
    ⟨taggedIncidence, taggedSelected, occurrenceEq⟩
  subst occurrence
  have taggedMember :
      taggedIncidence ∈
        (PeriodicCNF.incidencesWithMetadata source).zipIdx :=
    (List.mem_filter.mp taggedSelected).1
  have normalized :=
    externalWrappedVariableNormalization_sourceTerminal_eq
      source wellFormed taggedIncidence taggedMember site.2
  simp [PeriodicEquality.periodicizeLiteral, normalized]

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
