/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataLocalRouteLookup

/-! # Resolving indexed metadata clause descriptors locally -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

theorem indexedMetadataClauseDescriptor_eq_local_of_lookup
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedMetadata : DrawingPlanarSATClauseMetadata Variable × Nat)
    (metadataLookup :
      (retainedDrawingPlanarSATClauseMetadata source)[taggedMetadata.2]? =
        some taggedMetadata.1) :
    indexedMetadataClauseDescriptor source taggedMetadata =
      metadataClauseDescriptor source taggedMetadata.1 := by
  rcases taggedMetadata with ⟨metadata, clauseIndex⟩
  apply congrArg FormulaShapeDirectionOrdering.Token.clause
  unfold FormulaShapeDirectionOrdering.DirectedClauseProfile.ofClause
    FormulaShapeDirectionOrdering.annotatedLiterals
  apply congrArg FormulaShapeDirectionOrdering.DirectedClauseProfile.ofList
  apply List.map_congr_left
  intro taggedLiteral _taggedLiteralMember
  apply Prod.ext
  · rfl
  · rw [retainedLocalIncidenceRoute_eq_of_metadataLookup
      source metadata clauseIndex taggedLiteral.2 metadataLookup]

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
