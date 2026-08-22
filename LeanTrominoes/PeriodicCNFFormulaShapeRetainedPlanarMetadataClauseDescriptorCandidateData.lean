/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataDescriptorBlockData

/-! # Candidate retained metadata clause descriptors -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- The finite descriptor attached to a normalized metadata clause at a
specified source-presentation index. -/
def metadataClauseDescriptorAt {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clause : PeriodicClause (WrappedPeriodicPlanarSATVariable Variable))
    (sourceClauseIndex : Nat) :
    FormulaShapeDirectionOrdering.Token :=
  .clause
    (FormulaShapeDirectionOrdering.DirectedClauseProfile.ofClause
      (retainedDrawingPlanarSATLocalIncidenceRoutes source)
      sourceClauseIndex ⟨(0, 0), clause⟩)

/-- One candidate descriptor for every normalized metadata clause, before
removing repeated normalized clause orbits. -/
def metadataClauseDescriptorCandidates {Variable : Type}
    [DecidableEq Variable] (source : PeriodicCNF Variable) :
    List FormulaShapeDirectionOrdering.Token :=
  (normalizedClauses source).zipIdx.map fun taggedClause =>
    metadataClauseDescriptorAt source taggedClause.1 taggedClause.2

/-- The raw-route descriptor attached to one indexed retained clause. -/
def rawIndexedClauseDescriptor {Variable : Type}
    [DecidableEq Variable] (source : PeriodicCNF Variable) :
    PeriodicClause (WrappedPeriodicPlanarSATVariable Variable) × Nat →
      FormulaShapeDirectionOrdering.Token
  | (clause, clauseIndex) =>
      .clause
        (FormulaShapeDirectionOrdering.DirectedClauseProfile.ofClause
          (rawRepresentativeRoute source) clauseIndex
          ⟨(0, 0), clause⟩)

/-- The public raw-route descriptor expression, exposed as an indexed map
over the deduplicated normalized clauses. -/
def rawIndexedClauseDescriptors {Variable : Type}
    [DecidableEq Variable] (source : PeriodicCNF Variable) :
    List FormulaShapeDirectionOrdering.Token :=
  (deduplicatedClauses source).zipIdx.map
    (rawIndexedClauseDescriptor source)

/-- The candidate selected through the first normalized source occurrence
of a retained clause. -/
def representativeClauseDescriptor {Variable : Type}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (clause : PeriodicClause (WrappedPeriodicPlanarSATVariable Variable)) :
    FormulaShapeDirectionOrdering.Token :=
  metadataClauseDescriptorAt source clause
    ((normalizedClauses source).idxOf clause)

/-- Representative descriptors in the exact last-occurrence-preserving
deduplication order. -/
def representativeClauseDescriptors {Variable : Type}
    [DecidableEq Variable] (source : PeriodicCNF Variable) :
    List FormulaShapeDirectionOrdering.Token :=
  (deduplicatedClauses source).map
    (representativeClauseDescriptor source)

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
