/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataClauseDescriptorCandidateData

/-! # Clause descriptors attached directly to retained metadata records -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- The finite descriptor read directly from one retained clause metadata
record and its local component drawing. -/
def metadataClauseDescriptor {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (metadata : DrawingPlanarSATClauseMetadata Variable) :
    FormulaShapeDirectionOrdering.Token :=
  .clause
    (FormulaShapeDirectionOrdering.DirectedClauseProfile.ofClause
      (metadata.source.incidenceDrawing source).routes
      metadata.source.localClauseIndex
      ⟨(0, 0), normalizedClause source metadata⟩)

/-- The candidate expression before resolving its global metadata lookup to
the record's local component drawing. -/
def indexedMetadataClauseDescriptor {Variable : Type}
    [DecidableEq Variable] (source : PeriodicCNF Variable) :
    DrawingPlanarSATClauseMetadata Variable × Nat →
      FormulaShapeDirectionOrdering.Token
  | (metadata, clauseIndex) =>
      metadataClauseDescriptorAt source
        (normalizedClause source metadata) clauseIndex

/-- Global-indexed candidates presented directly over the retained metadata
records that generated their normalized clauses. -/
def indexedMetadataClauseDescriptors {Variable : Type}
    [DecidableEq Variable] (source : PeriodicCNF Variable) :
    List FormulaShapeDirectionOrdering.Token :=
  (retainedDrawingPlanarSATClauseMetadata source).zipIdx.map
    (indexedMetadataClauseDescriptor source)

/-- Direct local descriptors in the exact five-family retained metadata
presentation order. -/
def metadataMappedClauseDescriptors {Variable : Type}
    [DecidableEq Variable] (source : PeriodicCNF Variable) :
    List FormulaShapeDirectionOrdering.Token :=
  (retainedDrawingPlanarSATClauseMetadata source).map
    (metadataClauseDescriptor source)

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
