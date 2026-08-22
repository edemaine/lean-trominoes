/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataClauseDescriptorMetadataData

/-! # Local-route lookup through retained metadata -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

theorem retainedLocalIncidenceRoute_eq_of_metadataLookup
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (clauseIndex literalIndex : Nat)
    (metadataLookup :
      (retainedDrawingPlanarSATClauseMetadata source)[clauseIndex]? =
        some metadata) :
    retainedDrawingPlanarSATLocalIncidenceRoutes source
        clauseIndex literalIndex =
      (metadata.source.incidenceDrawing source).routes
        metadata.source.localClauseIndex literalIndex := by
  unfold retainedDrawingPlanarSATLocalIncidenceRoutes
  rw [metadataLookup]

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
