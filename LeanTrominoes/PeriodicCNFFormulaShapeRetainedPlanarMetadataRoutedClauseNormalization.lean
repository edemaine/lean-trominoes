/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedClauseData

/-! # Normalized retained routed source clauses -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- The normalized source-clause prototype obtained by applying the shared
external endpoint normalization directly to one routed clause. -/
def normalizedRoutedClauseAt
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (site : ClauseRouteSite) :
    PeriodicClause (WrappedPeriodicPlanarSATVariable Variable) :=
  (PeriodicEquality.periodicizeClause
    (externalWrappedVariableNormalization source)
    (routedClauseAt source site)).anchorNormalize

/-- The complete retained metadata normalization of a routed source clause
is exactly its shared external-endpoint normal form. -/
theorem normalizedClause_routedClauseMetadataAt_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (site : ClauseRouteSite) :
    normalizedClause source (routedClauseMetadataAt source site) =
      normalizedRoutedClauseAt source site := by
  simp [normalizedClause, routedClauseMetadataAt,
    normalizedRoutedClauseAt,
    periodicizePlanarSATClause, periodicizePlanarSATLiteral,
    planarSATExternalVariableMap,
    EmbeddedClause.rename, EmbeddedClause.map,
    wrapPeriodicPlanarSATClause, wrapPeriodicPlanarSATLiteral,
    PeriodicEquality.periodicizeClause,
    PeriodicClause.variableGauge,
    PeriodicLiteral.variableGauge,
    List.map_map, Function.comp_def]
  congr 1

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
