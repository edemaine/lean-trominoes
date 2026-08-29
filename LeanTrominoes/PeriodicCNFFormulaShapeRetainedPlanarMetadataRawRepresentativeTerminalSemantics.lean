/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataLocalRouteLookup
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRawRoutes
import LeanTrominoes.PeriodicEightOccurrenceSplitTerminalPorts

/-! # Raw representative terminal vectors from metadata -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing
open PeriodicThreeSATThree

/-- An exact clause and first-metadata lookup identify the raw representative
route's terminal vector with that metadata source's local route. -/
theorem rawRepresentativeRoute_routeTerminalVector_eq_metadata
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat)
    (clause :
      PeriodicClause (WrappedPeriodicPlanarSATVariable Variable))
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (clauseLookup :
      (deduplicatedClauses source)[clauseIndex]? = some clause)
    (metadataLookup :
      (retainedDrawingPlanarSATClauseMetadata source)[
          (normalizedClauses source).idxOf clause]? = some metadata) :
    routeTerminalVector
        (rawRepresentativeRoute source clauseIndex literalIndex) =
      routeTerminalVector
        ((metadata.source.incidenceDrawing source).routes
          metadata.source.localClauseIndex literalIndex) := by
  unfold rawRepresentativeRoute
  rw [clauseLookup]
  dsimp only
  have routeEq :
      retainedDrawingPlanarSATLocalIncidenceRoutes source
          ((normalizedClauses source).idxOf clause) literalIndex =
        (metadata.source.incidenceDrawing source).routes
          metadata.source.localClauseIndex literalIndex :=
    retainedLocalIncidenceRoute_eq_of_metadataLookup
      source metadata ((normalizedClauses source).idxOf clause)
        literalIndex metadataLookup
  exact congrArg routeTerminalVector routeEq

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
