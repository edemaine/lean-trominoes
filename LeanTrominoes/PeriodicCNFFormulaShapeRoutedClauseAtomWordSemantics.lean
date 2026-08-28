/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedClauseNormalizedFamilyDeduplication

/-! # Atom-word column of normalized routed clauses -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Normalizing a routed source clause changes offsets but preserves the
presentation-ordered source-terminal prototypes of its route occurrences. -/
theorem normalizedRoutedClauseAt_atomWords
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (site : ClauseRouteSite)
    (word : WrappedPeriodicPlanarSATVariable Variable → List Bool) :
    (normalizedRoutedClauseAt source site).map
        (fun literal => word literal.atom) =
      (clauseRouteOccurrencesAt source site).map fun occurrence =>
        word (externalWrappedVariableNormalization source
          (.carrier (.terminal
            (occurrence.sourceTerminal source)))).1 := by
  simp [normalizedRoutedClauseAt, routedClauseAt,
    PeriodicEquality.periodicizeClause,
    PeriodicEquality.periodicizeLiteral,
    PeriodicClause.anchorNormalize,
    PeriodicLiteral.anchorNormalize,
    List.map_map, Function.comp_def]

/-- The complete base routed-clause family is the clause-major flattening of
those normalized source-terminal word rows. -/
theorem baseRoutedClauseNormalizedClauses_atomWords
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (word : WrappedPeriodicPlanarSATVariable Variable → List Bool) :
    (baseRoutedClauseNormalizedClauses source).flatMap
        (fun clause => clause.map fun literal => word literal.atom) =
      source.clauses.zipIdx.flatMap fun taggedClause =>
        (clauseRouteOccurrencesAt source
          (taggedClause.2, (0, 0))).map fun occurrence =>
            word (externalWrappedVariableNormalization source
              (.carrier (.terminal
                (occurrence.sourceTerminal source)))).1 := by
  unfold baseRoutedClauseNormalizedClauses
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro taggedClause _taggedClauseMember
  exact normalizedRoutedClauseAt_atomWords
    source (taggedClause.2, (0, 0)) word

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
